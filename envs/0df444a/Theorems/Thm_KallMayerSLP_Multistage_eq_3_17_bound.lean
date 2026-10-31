-- Prove2me | Theorems.Thm_KallMayerSLP_Multistage_eq_3_17_bound
-- name    : KallMayerSLP.Multistage.eq_3_17_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:22:43.69293+00:00
-- url     : https://prove2.me/theorems/03ad65a5-249e-4083-9185-8ba03c2624e6
-- title:
--   The induction step of Lemma 3.1: $q_t\le r_t$ and $\Psi_{t+1}\le\Phi_{t+1}$
-- statement:
--   Let (3.10) satisfy Assumption 3.2 and take a scenario tree. At every node $n$ of every stage $t$, for all $z$,
--   $$
--   q_t\big(z_{t-1};\widehat\zeta^n\big)\le r_t\big(z_{t-1};\widehat\zeta^n\big),\qquad\Psi_{t+1}\big(z_t;\widehat\zeta^n\big)\le\Phi_{t+1}\big(z_t;\widehat\zeta^n\big).
--   $$
--
--   This is the bound the book propagates backwards through the stages, starting from $\Psi_{T+1}\equiv\Phi_{T+1}\equiv0$. At the root it yields $q_1\le r_1$.
--
--   **Formalization Note** The realization is any full family whose coordinates up to stage $t$ are $\widehat\zeta^n$. The Lean `Psi` at a node of stage $t$ is the book's $\Psi_{t+1}$.
--
--   Differences from the source:
--   - reading: Assumption 3.2: the A_tt complete fixed recourse matrices ∀t → complete recourse of A_tt for t = 2, …, T; reason: A_11 is not a recourse matrix, and the book's Example 3.1 calls a problem with a non-complete first stage complete fixed recourse; this is the weaker hypothesis, so the statement implies the ∀t one
--   - generalization: supp ℙ_{ξ_t} ⊆ Ξ^t → ξ_t ∈ Ξ^t almost surely; reason: the support inclusion implies the almost sure one, and they agree for closed Ξ^t, so the statement specializes to the source
--   - encoding: z_{t-1} and ζ̂_t as finite sequences → full families z and w, of which only the coordinates the book lists are used; reason: the same functions; unused coordinates have no effect
--   - generalization: provided Ψ_{t+1} ≤ Φ_{t+1}, then q_t ≤ r_t (and Ψ_t ≤ Φ_t) → q_t ≤ r_t and Ψ_{t+1} ≤ Φ_{t+1} at every node of every stage, unconditionally; reason: the proviso holds by the book's own backward induction from Ψ_{T+1} ≡ Φ_{T+1} ≡ 0, so the statement implies the conditional step
--   - generalization: a partition of Ξ^{ν+1} into subintervals, |C_n| = r_n ≥ 1 → ScenarioTree, whose cells may be empty (a node may then have no child when Ξ^{ν+1} is empty); reason: every tree of p.261 is a ScenarioTree, so the statement specializes to the book's trees
--   - encoding: ξ̄^n_t = 𝔼[ξ_t | ξ_t ∈ Ξ^t_n], undefined on a P-null cell → xiBar = 0 on a P-null cell (Lean's 0⁻¹ = 0); reason: such a node and its descendants have p_n = 0, and their constraints are solvable by complete recourse of A_tt (t ≥ 2), so no value of (3.14) depends on the choice
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, pp.264–265 (PDF 273–274)

import Mathlib
import Definitions.Def_KallMayerSLP_Multistage_Assumption32
import Definitions.Def_KallMayerSLP_Multistage_qFn
import Definitions.Def_KallMayerSLP_Multistage_rFn

namespace KallMayerSLP.Multistage

open MeasureTheory

/-- **Chapter 3, the induction step of Lemma 3.1** (Kall & Mayer, *Stochastic Linear Programming*
(2005), Chapter 3, p.264, PDF 273 – p.265, PDF 274): at every node `n` of every stage `t`, and with
`ζ̂_t` the realization of `n`, the aggregated quantities bound the original ones,
`q_t(z_{t-1}; ζ̂^n) ≤ r_t(z_{t-1}; ζ̂^n)` and `Ψ_{t+1}(z_t; ζ̂^n) ≤ Φ_{t+1}(z_t; ζ̂^n)`.

**Formalization Note.** `w` is any full family of realizations whose coordinates up to `t` are
`ζ̂^n`. `Psi 𝒯 P ξ t n` is the book's `Ψ_{t+1}` at `n`. -/
theorem eq_3_17_bound {D : MSLP} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ξ : ∀ t, Ω → Fin (D.r t) → ℝ} {Ξ : ∀ t, Set (Fin (D.r t) → ℝ)}
    (hA : Assumption32 D P ξ Ξ) (𝒯 : ScenarioTree D Ξ) {t : ℕ} (ht₁ : 1 ≤ t) (ht : t ≤ D.T)
    (n : 𝒯.Node t) (z : ∀ τ, Fin (D.n τ) → ℝ) (w : ∀ s, Fin (D.r s) → ℝ)
    (hw : toHist t w = zetaHat 𝒯 P ξ n) :
    qFn 𝒯 P ξ t n z ≤ rFn D (fun t => P.map (ξ t)) t z w ∧
      Psi 𝒯 P ξ t n z ≤ Phi D (fun t => P.map (ξ t)) (t + 1) z w := by sorry

end KallMayerSLP.Multistage
