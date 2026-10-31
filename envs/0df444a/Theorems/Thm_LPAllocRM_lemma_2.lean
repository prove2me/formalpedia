-- Prove2me | Theorems.Thm_LPAllocRM_lemma_2
-- name    : LPAllocRM.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:09:31.32618+00:00
-- url     : https://prove2.me/theorems/5fe7d48b-4631-4a5f-9658-c5acf81cb077
-- title:
--   Lemma 2: $ER^{LP(k)}\le v^{(k)}\le k\beta$
-- statement:
--   Throughout, the model is that of §2–§4 of the paper. There are $m$ resources with capacities $c_i>0$ and $n$ products; a class-$j$ customer consumes $a_{ij}\ge 0$ units of resource $i$ and pays the fare $f_j$ (of any sign). Requests arrive one at a time over $(0,\tau]$, $\tau>0$. $x^*$ is an optimal solution of the linear program (3) $\max\{f\cdot x : Ax\le c,\ 0\le x\le\mu\}$ and $\beta=f\cdot x^*$. Problem $k=1,2,\dots$ has capacity $kc$ and its own arrival process $D^{(k)}(\cdot)$ on a probability space $(\Omega_k,P_k)$, with (a) finitely many arrivals and (b) at most one arrival at any time almost surely, and $ED^{(k)}(\tau)=k\mu$. $R^{LP(k)}$ is the revenue of the allocation policy $\pi^{LP(k)}_j(t)=1(D^{(k)}_j(t)\le kx^*_j)$ in problem $k$, and $v^{(k)}$ is the value (1) of problem $k$, the supremum of $E(f\cdot N^{\pi})$ over all history-dependent policies $\pi$ with $AN^{\pi}\le kc$ almost surely.
--
--   Then for all $k\ge 1$,
--
--   $$ER^{LP(k)}\le v^{(k)}\le k\beta.$$
--
--   The first inequality says that the LP policy is one of the admissible policies; the second, that no policy, however it uses the history, earns more in expectation than the deterministic LP (6). Condition (7) is not needed.
--
--   Differences from the source:
--   - encoding: the arrival process D(·) is a random simple point process on (0, τ] with finitely many points a.s. → D k ω : ℝ → Fin n → ℕ counting paths, each count ω ↦ D k ω t j measurable, IsArrivalPath τ (D k ω) a.s.; reason: a simple point process with finitely many points is the same as its counting path; the two descriptions have the same instances
--   - encoding: N^π_j ≡ ∫_(0,τ] π_j(s) D_j(ds), (2) → accepted: the number of i ∈ {1, …, D_j(τ)} such that π accepts class j at the i-th class-j arrival time, given the path up to that time; reason: on a simple counting path the Stieltjes integral (2) is exactly this count
--   - encoding: Π: maps from the history up to t to {0,1}^n → Policy n: functions of t and of the arrival path restricted to (−∞, t] (closed at t) to Fin n → Bool; reason: the same class of nonanticipating history-dependent rules; the history includes an arrival at t, as on p.723
--   - encoding: problems k = 1, 2, … (k ⩾ 1) → k : ℕ+, limits along atTop on ℕ+; reason: same index set; there is no problem k = 0
--   - encoding: μ ≡ ED(τ) of the original problem, μ < ∞, and ED^(k)(τ) = kμ → μ : Fin n → ℝ with D^(k)_j(τ) integrable and ∫ D^(k)_j(τ) dP_k = kμ_j for every k ≥ 1; reason: at k = 1 the hypothesis makes μ the expected demand of the original problem; finiteness of the mean is integrability
--   - encoding: N^π is "the random variable" (2) whose expectation enters (1) → Admissible requires each ω ↦ N^π_j to be AEMeasurable; reason: E(f · N^π) in (1) is only defined for random variables
--   - encoding: v ≡ sup over π ∈ Π of E(f · N^π) subject to AN^π ⩽ kc, 0 ⩽ N^π ⩽ D(τ) a.s., (1) → value: real sSup of the Bochner expectations of revenue over admissible policies; reason: the set is nonempty (π^LP and the reject-all policy are admissible) and bounded above by kβ, so sSup is the paper's supremum
-- source:
--   Cooper, Asymptotic Behavior of an Allocation Policy for Revenue Management, Operations Research 50(4) (2002), doi:10.1287/opre.50.4.720.2855, Lemma 2, p.724

import Mathlib
import Definitions.Def_LPAllocRM_IsLPOptimal
import Definitions.Def_LPAllocRM_IsScaledFamily
import Definitions.Def_LPAllocRM_lpPolicy
import Definitions.Def_LPAllocRM_revenue
import Definitions.Def_LPAllocRM_value
import Definitions.Def_LPAllocRM_Admissible
open MeasureTheory Filter Topology Matrix

namespace LPAllocRM

/-- Lemma 2: `E R^LP(k) ≤ v^(k) ≤ k β` for all `k ≥ 1`, where `v^(k)` is the value (1) of the kth
problem and `β = f · x*`.
Cooper, *Asymptotic Behavior of an Allocation Policy for Revenue Management*, Operations Research 50(4) (2002), doi:10.1287/opre.50.4.720.2855,
Lemma 2, p.724 (PDF p.5).

The model: `m` resources with capacities `c_i > 0`, `n` products with consumption `a_ij ≥ 0`
and fares `f_j` of any sign, horizon `(0, τ]` with `τ > 0`, an optimal solution `x*` of the LP (3)
`max {f · x : A x ≤ c, 0 ≤ x ≤ μ}`, and the scaled problems `k = 1, 2, …` (capacity `k c`, arrival
process `D^(k)` on its own probability space `(Ω k, P k)` satisfying (a), (b) and `E D^(k)(τ) = k μ`).
`R^LP(k)` is the revenue of `lpPolicy (k • x*)` on `D^(k)`, and `v^(k)` is `value A (k • c) …`, the
supremum (1) over all history-dependent policies.

**Formalization Note** `v^(k)` is the real `sSup` of the expected revenues of all admissible
policies (`value`). Condition (7) is not assumed: Lemma 2 holds for every problem of the family. -/
theorem lemma_2 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin m → ℝ) (f : Fin n → ℝ) (τ : ℝ)
    (μ : Fin n → ℝ) (xstar : Fin n → ℝ)
    (hc : ∀ i, 0 < c i) (hA : ∀ i j, 0 ≤ A i j) (hτ : 0 < τ)
    (hx : IsLPOptimal A c μ f xstar)
    {Ω : ℕ+ → Type*} [∀ k, MeasurableSpace (Ω k)] (P : ∀ k, Measure (Ω k))
    [∀ k, IsProbabilityMeasure (P k)] (D : ∀ k, Ω k → ℝ → Fin n → ℕ)
    (hD : IsScaledFamily τ μ P D) :
    ∀ k : ℕ+,
      ∫ ω, revenue f τ (lpPolicy (((k : ℕ) : ℝ) • xstar)) (D k ω) ∂(P k) ≤
          value A (((k : ℕ) : ℝ) • c) f τ (P k) (D k) ∧
        value A (((k : ℕ) : ℝ) • c) f τ (P k) (D k) ≤ ((k : ℕ) : ℝ) * (f ⬝ᵥ xstar) := by sorry

end LPAllocRM
