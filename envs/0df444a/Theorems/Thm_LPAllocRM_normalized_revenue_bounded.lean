-- Prove2me | Theorems.Thm_LPAllocRM_normalized_revenue_bounded
-- name    : LPAllocRM.normalized_revenue_bounded
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:09:43.551246+00:00
-- url     : https://prove2.me/theorems/3883a9e6-72ab-4011-a843-221b8c5222fb
-- title:
--   The normalized revenues $k^{-1}R^{LP(k)}$ are bounded by $\beta$
-- statement:
--   Throughout, the model is that of §2–§4 of the paper. There are $m$ resources with capacities $c_i>0$ and $n$ products; a class-$j$ customer consumes $a_{ij}\ge 0$ units of resource $i$ and pays the fare $f_j$ (of any sign). Requests arrive one at a time over $(0,\tau]$, $\tau>0$. $x^*$ is an optimal solution of the linear program (3) $\max\{f\cdot x : Ax\le c,\ 0\le x\le\mu\}$ and $\beta=f\cdot x^*$. Problem $k=1,2,\dots$ has capacity $kc$ and its own arrival process $D^{(k)}(\cdot)$ on a probability space $(\Omega_k,P_k)$, with (a) finitely many arrivals and (b) at most one arrival at any time almost surely, and $ED^{(k)}(\tau)=k\mu$. $R^{LP(k)}$ is the revenue of the allocation policy $\pi^{LP(k)}_j(t)=1(D^{(k)}_j(t)\le kx^*_j)$ in problem $k$, and $v^{(k)}$ is the value (1) of problem $k$, the supremum of $E(f\cdot N^{\pi})$ over all history-dependent policies $\pi$ with $AN^{\pi}\le kc$ almost surely.
--
--   Then for every $k=1,2,\dots$, almost surely
--
--   $$\bigl|k^{-1}R^{LP(k)}\bigr|\le\beta.$$
--
--   That is, the random variables $k^{-1}R^{LP(k)}$ are uniformly bounded by the number $\beta$, which is what turns convergence in distribution into convergence of expectations in Proposition 1(ii).
--
--   Differences from the source:
--   - encoding: the arrival process D(·) is a random simple point process on (0, τ] with finitely many points a.s. → D k ω : ℝ → Fin n → ℕ counting paths, each count ω ↦ D k ω t j measurable, IsArrivalPath τ (D k ω) a.s.; reason: a simple point process with finitely many points is the same as its counting path; the two descriptions have the same instances
--   - encoding: N^π_j ≡ ∫_(0,τ] π_j(s) D_j(ds), (2) → accepted: the number of i ∈ {1, …, D_j(τ)} such that π accepts class j at the i-th class-j arrival time, given the path up to that time; reason: on a simple counting path the Stieltjes integral (2) is exactly this count
--   - encoding: Π: maps from the history up to t to {0,1}^n → Policy n: functions of t and of the arrival path restricted to (−∞, t] (closed at t) to Fin n → Bool; reason: the same class of nonanticipating history-dependent rules; the history includes an arrival at t, as on p.723
--   - encoding: problems k = 1, 2, … (k ⩾ 1) → k : ℕ+, limits along atTop on ℕ+; reason: same index set; there is no problem k = 0
--   - encoding: μ ≡ ED(τ) of the original problem, μ < ∞, and ED^(k)(τ) = kμ → μ : Fin n → ℝ with D^(k)_j(τ) integrable and ∫ D^(k)_j(τ) dP_k = kμ_j for every k ≥ 1; reason: at k = 1 the hypothesis makes μ the expected demand of the original problem; finiteness of the mean is integrability
--   - encoding: "uniformly bounded (by the number β)" → for every k, |k⁻¹R^LP(k)| ⩽ β almost surely; reason: the model's path assumptions hold almost surely, so the bound is an almost-sure one
-- source:
--   Cooper, Asymptotic Behavior of an Allocation Policy for Revenue Management, Operations Research 50(4) (2002), doi:10.1287/opre.50.4.720.2855, proof of Proposition 1, p.724

import Mathlib
import Definitions.Def_LPAllocRM_IsLPOptimal
import Definitions.Def_LPAllocRM_IsScaledFamily
import Definitions.Def_LPAllocRM_lpPolicy
import Definitions.Def_LPAllocRM_revenue
import Definitions.Def_LPAllocRM_value
import Definitions.Def_LPAllocRM_Admissible
open MeasureTheory Filter Topology Matrix

namespace LPAllocRM

/-- The normalized revenues `k^{-1} R^LP(k)` are uniformly bounded by the number `β = f · x*`:
for every `k`, almost surely `|k^{-1} R^LP(k)| ≤ β`.
Cooper, *Asymptotic Behavior of an Allocation Policy for Revenue Management*, Operations Research 50(4) (2002), doi:10.1287/opre.50.4.720.2855,
proof of Proposition 1, p.724 (PDF p.5): "The random variables k^{−1}R^{LP(k)} are uniformly bounded
(by the number β)".

The model: `m` resources with capacities `c_i > 0`, `n` products with consumption `a_ij ≥ 0`
and fares `f_j` of any sign, horizon `(0, τ]` with `τ > 0`, an optimal solution `x*` of the LP (3)
`max {f · x : A x ≤ c, 0 ≤ x ≤ μ}`, and the scaled problems `k = 1, 2, …` (capacity `k c`, arrival
process `D^(k)` on its own probability space `(Ω k, P k)` satisfying (a), (b) and `E D^(k)(τ) = k μ`).
`R^LP(k)` is the revenue of `lpPolicy (k • x*)` on `D^(k)`, and `v^(k)` is `value A (k • c) …`, the
supremum (1) over all history-dependent policies.

**Formalization Note** No sign condition on the fares is assumed (the paper states none). -/
theorem normalized_revenue_bounded {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin m → ℝ) (f : Fin n → ℝ) (τ : ℝ)
    (μ : Fin n → ℝ) (xstar : Fin n → ℝ)
    (hc : ∀ i, 0 < c i) (hA : ∀ i j, 0 ≤ A i j) (hτ : 0 < τ)
    (hx : IsLPOptimal A c μ f xstar)
    {Ω : ℕ+ → Type*} [∀ k, MeasurableSpace (Ω k)] (P : ∀ k, Measure (Ω k))
    [∀ k, IsProbabilityMeasure (P k)] (D : ∀ k, Ω k → ℝ → Fin n → ℕ)
    (hD : IsScaledFamily τ μ P D) :
    ∀ k : ℕ+, ∀ᵐ ω ∂(P k),
      |((k : ℕ) : ℝ)⁻¹ * revenue f τ (lpPolicy (((k : ℕ) : ℝ) • xstar)) (D k ω)| ≤
        f ⬝ᵥ xstar := by sorry

end LPAllocRM
