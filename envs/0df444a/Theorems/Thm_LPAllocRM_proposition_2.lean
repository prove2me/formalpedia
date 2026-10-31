-- Prove2me | Theorems.Thm_LPAllocRM_proposition_2
-- name    : LPAllocRM.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:09:22.842348+00:00
-- url     : https://prove2.me/theorems/eff98189-1865-4a38-ae8a-74ab65270850
-- title:
--   Proposition 2: $R^{LP(k)}/v^{(k)}\to1$ in distribution and $ER^{LP(k)}/v^{(k)}\to1$
-- statement:
--   Throughout, the model is that of §2–§4 of the paper. There are $m$ resources with capacities $c_i>0$ and $n$ products; a class-$j$ customer consumes $a_{ij}\ge 0$ units of resource $i$ and pays the fare $f_j$ (of any sign). Requests arrive one at a time over $(0,\tau]$, $\tau>0$. $x^*$ is an optimal solution of the linear program (3) $\max\{f\cdot x : Ax\le c,\ 0\le x\le\mu\}$ and $\beta=f\cdot x^*$. Problem $k=1,2,\dots$ has capacity $kc$ and its own arrival process $D^{(k)}(\cdot)$ on a probability space $(\Omega_k,P_k)$, with (a) finitely many arrivals and (b) at most one arrival at any time almost surely, and $ED^{(k)}(\tau)=k\mu$. $R^{LP(k)}$ is the revenue of the allocation policy $\pi^{LP(k)}_j(t)=1(D^{(k)}_j(t)\le kx^*_j)$ in problem $k$, and $v^{(k)}$ is the value (1) of problem $k$, the supremum of $E(f\cdot N^{\pi})$ over all history-dependent policies $\pi$ with $AN^{\pi}\le kc$ almost surely.
--
--   Suppose that (7) holds,
--
--   $$k^{-1}D^{(k)}(\tau)\xrightarrow{\mathcal D}\mu,$$
--
--   and that $\beta=f\cdot x^*>0$. Then, as $k\to\infty$,
--
--   1. $R^{LP(k)}/v^{(k)}\xrightarrow{\mathcal D}1$, and
--   2. $ER^{LP(k)}/v^{(k)}\to1$.
--
--   This is the paper's primary result: the single-LP allocation policy is asymptotically optimal among all history-dependent policies, both for the distribution of its revenue and in expectation, when capacities and expected demands grow proportionally.
--
--   Differences from the source:
--   - encoding: the arrival process D(·) is a random simple point process on (0, τ] with finitely many points a.s. → D k ω : ℝ → Fin n → ℕ counting paths, each count ω ↦ D k ω t j measurable, IsArrivalPath τ (D k ω) a.s.; reason: a simple point process with finitely many points is the same as its counting path; the two descriptions have the same instances
--   - encoding: N^π_j ≡ ∫_(0,τ] π_j(s) D_j(ds), (2) → accepted: the number of i ∈ {1, …, D_j(τ)} such that π accepts class j at the i-th class-j arrival time, given the path up to that time; reason: on a simple counting path the Stieltjes integral (2) is exactly this count
--   - encoding: Π: maps from the history up to t to {0,1}^n → Policy n: functions of t and of the arrival path restricted to (−∞, t] (closed at t) to Fin n → Bool; reason: the same class of nonanticipating history-dependent rules; the history includes an arrival at t, as on p.723
--   - encoding: problems k = 1, 2, … (k ⩾ 1) → k : ℕ+, limits along atTop on ℕ+; reason: same index set; there is no problem k = 0
--   - encoding: μ ≡ ED(τ) of the original problem, μ < ∞, and ED^(k)(τ) = kμ → μ : Fin n → ℝ with D^(k)_j(τ) integrable and ∫ D^(k)_j(τ) dP_k = kμ_j for every k ≥ 1; reason: at k = 1 the hypothesis makes μ the expected demand of the original problem; finiteness of the mean is integrability
--   - encoding: N^π is "the random variable" (2) whose expectation enters (1) → Admissible requires each ω ↦ N^π_j to be AEMeasurable; reason: E(f · N^π) in (1) is only defined for random variables
--   - encoding: v ≡ sup over π ∈ Π of E(f · N^π) subject to AN^π ⩽ kc, 0 ⩽ N^π ⩽ D(τ) a.s., (1) → value: real sSup of the Bochner expectations of revenue over admissible policies; reason: the set is nonempty (π^LP and the reject-all policy are admissible) and bounded above by kβ, so sSup is the paper's supremum
--   - encoding: X_k →^D X: lim P_k(X_k ∈ S) = P(X ∈ S) for every X-continuity set S (p.723) → Mathlib TendstoInDistribution: weak convergence of the laws, with each X_k almost-everywhere measurable; reason: equivalent by the portmanteau theorem
--   - encoding: constant limits (μ in (7), β, 1) → constant functions on the one-point space Unit under Measure.dirac (); reason: a constant random variable; the paper itself writes β as a random variable with P(β = f · x*) = 1
--   - encoding: R^LP(k)/v^(k) with no condition on β → hypothesis β = f · x* > 0; reason: β ⩾ 0 always (x = 0 is feasible), and β = 0 forces v^(k) = R^LP(k) = 0 for every k, where every ratio is 0/0; the hypothesis only excludes that undefined case
--   - encoding: ratios with denominator v^(k) → Lean real division (x/0 = 0); reason: v^(k) ⩾ ER^LP(k) and k⁻¹ER^LP(k) → β > 0 give v^(k) > 0 for all large k, so at most finitely many indices are affected and the limits are the paper's
-- source:
--   Cooper, Asymptotic Behavior of an Allocation Policy for Revenue Management, Operations Research 50(4) (2002), doi:10.1287/opre.50.4.720.2855, Proposition 2, p.725; condition (7), p.723; v^(k) from eq. (1), p.722

import Mathlib
import Definitions.Def_LPAllocRM_IsLPOptimal
import Definitions.Def_LPAllocRM_IsScaledFamily
import Definitions.Def_LPAllocRM_lpPolicy
import Definitions.Def_LPAllocRM_revenue
import Definitions.Def_LPAllocRM_value
import Definitions.Def_LPAllocRM_Admissible
open MeasureTheory Filter Topology Matrix

namespace LPAllocRM

/-- Proposition 2: suppose (7), `k^{-1} D^(k)(τ) → μ` in distribution, and `β = f · x* > 0`. Then
(i) `R^LP(k) / v^(k) → 1` in distribution, and (ii) `E R^LP(k) / v^(k) → 1`, as `k → ∞`.
Cooper, *Asymptotic Behavior of an Allocation Policy for Revenue Management*, Operations Research 50(4) (2002), doi:10.1287/opre.50.4.720.2855,
Proposition 2, p.725 (PDF p.6); condition (7), p.723 (PDF p.4); `v^(k)` from (1), p.722.

The model: `m` resources with capacities `c_i > 0`, `n` products with consumption `a_ij ≥ 0`
and fares `f_j` of any sign, horizon `(0, τ]` with `τ > 0`, an optimal solution `x*` of the LP (3)
`max {f · x : A x ≤ c, 0 ≤ x ≤ μ}`, and the scaled problems `k = 1, 2, …` (capacity `k c`, arrival
process `D^(k)` on its own probability space `(Ω k, P k)` satisfying (a), (b) and `E D^(k)(τ) = k μ`).
`R^LP(k)` is the revenue of `lpPolicy (k • x*)` on `D^(k)`, and `v^(k)` is `value A (k • c) …`, the
supremum (1) over all history-dependent policies.

**Formalization Note** `β > 0` excludes the degenerate case in which the ratios are `0/0`
(for instance `f = 0` gives `R^LP(k) = v^(k) = 0`); the paper divides by `v^(k)` without comment.
Division is Lean's real division (`x / 0 = 0`); since `v^(k) ≥ E R^LP(k)` and `k^{-1} E R^LP(k) → β > 0`,
`v^(k) > 0` for all large `k`, so this affects at most finitely many indices and not the limits.
Convergence in distribution is `TendstoInDistribution`, the constant limit `1` a constant random
variable on `Unit` under the Dirac measure. -/
theorem proposition_2 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin m → ℝ) (f : Fin n → ℝ) (τ : ℝ)
    (μ : Fin n → ℝ) (xstar : Fin n → ℝ)
    (hc : ∀ i, 0 < c i) (hA : ∀ i j, 0 ≤ A i j) (hτ : 0 < τ)
    (hx : IsLPOptimal A c μ f xstar)
    {Ω : ℕ+ → Type*} [∀ k, MeasurableSpace (Ω k)] (P : ∀ k, Measure (Ω k))
    [∀ k, IsProbabilityMeasure (P k)] (D : ∀ k, Ω k → ℝ → Fin n → ℕ)
    (hD : IsScaledFamily τ μ P D)
    (h7 : TendstoInDistribution (fun (k : ℕ+) (ω : Ω k) (j : Fin n) => ((k : ℕ) : ℝ)⁻¹ * (D k ω τ j : ℝ))
      atTop (fun _ : Unit => μ) P (Measure.dirac ()))
    (hβ : 0 < f ⬝ᵥ xstar) :
    TendstoInDistribution
        (fun (k : ℕ+) (ω : Ω k) =>
          revenue f τ (lpPolicy (((k : ℕ) : ℝ) • xstar)) (D k ω) /
            value A (((k : ℕ) : ℝ) • c) f τ (P k) (D k))
        atTop (fun _ : Unit => (1 : ℝ)) P (Measure.dirac ()) ∧
      Tendsto
        (fun k : ℕ+ =>
          (∫ ω, revenue f τ (lpPolicy (((k : ℕ) : ℝ) • xstar)) (D k ω) ∂(P k)) /
            value A (((k : ℕ) : ℝ) • c) f τ (P k) (D k))
        atTop (𝓝 1) := by sorry

end LPAllocRM
