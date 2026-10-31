-- Prove2me | Theorems.Thm_KallMayerSLP_Multistage_eq_3_17_value
-- name    : KallMayerSLP.Multistage.eq_3_17_value
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:22:17.527481+00:00
-- url     : https://prove2.me/theorems/b977c138-d2b4-4df4-a954-eb159d61ed42
-- title:
--   (3.17) — the aggregated recursion computes the optimal value of (3.14)
-- statement:
--   Let (3.10) satisfy Assumption 3.2 and take a scenario tree. With $\Psi_{T+1}\equiv0$ and the recursion (3.17) for $t=T,\dots,2$ at all nodes, the final value
--   $$
--   q_1:=\min_{x_1}\{c_1^{\mathsf T}x_1+\Psi_2(x_1;\widehat\zeta_1)\}\ \text{ s.t. }\ A_{11}x_1=b_1,\ x_1\ge0
--   $$
--   is the optimal value of the aggregated problem (3.14).
--
--   The large linear program (3.14) thus decomposes along the tree, in analogy with (3.15).
--
--   Differences from the source:
--   - reading: Assumption 3.2: the A_tt complete fixed recourse matrices ∀t → complete recourse of A_tt for t = 2, …, T; reason: A_11 is not a recourse matrix, and the book's Example 3.1 calls a problem with a non-complete first stage complete fixed recourse; this is the weaker hypothesis, so the statement implies the ∀t one
--   - generalization: supp ℙ_{ξ_t} ⊆ Ξ^t → ξ_t ∈ Ξ^t almost surely; reason: the support inclusion implies the almost sure one, and they agree for closed Ξ^t, so the statement specializes to the source
--   - encoding: min → infimum in EReal; reason: +∞ on infeasible and -∞ on unbounded problems; the book assumes neither case away
--   - encoding: z_{t-1} and ζ̂_t as finite sequences → full families z and w, of which only the coordinates the book lists are used; reason: the same functions; unused coordinates have no effect
--   - generalization: a partition of Ξ^{ν+1} into subintervals, |C_n| = r_n ≥ 1 → ScenarioTree, whose cells may be empty (a node may then have no child when Ξ^{ν+1} is empty); reason: every tree of p.261 is a ScenarioTree, so the statement specializes to the book's trees
--   - encoding: ξ̄^n_t = 𝔼[ξ_t | ξ_t ∈ Ξ^t_n], undefined on a P-null cell → xiBar = 0 on a P-null cell (Lean's 0⁻¹ = 0); reason: such a node and its descendants have p_n = 0, and their constraints are solvable by complete recourse of A_tt (t ≥ 2), so no value of (3.14) depends on the choice
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, (3.17) and the display after it, p.264 (PDF 273)

import Mathlib
import Definitions.Def_KallMayerSLP_Multistage_Assumption32
import Definitions.Def_KallMayerSLP_Multistage_aggValue
import Definitions.Def_KallMayerSLP_Multistage_qFn

namespace KallMayerSLP.Multistage

open MeasureTheory

/-- **Chapter 3, (3.17): the aggregated recursion computes the optimal value of (3.14)** (Kall &
Mayer, *Stochastic Linear Programming* (2005), Chapter 3, p.264, PDF 273): the recursion (3.17) gives
`q_1 := min_{x_1} {c_1ᵀ x_1 + Ψ_2(x_1; ζ̂_1)}` s.t. `A_11 x_1 = b_1(ζ̂_1) ≡ b_1`, `x_1 ≥ 0` "as the
optimal value of (3.14)".

**Formalization Note.** `root` is the unique node of stage 1. `q_1` does not depend on `z`, which
is universally quantified. -/
theorem eq_3_17_value {D : MSLP} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ξ : ∀ t, Ω → Fin (D.r t) → ℝ} {Ξ : ∀ t, Set (Fin (D.r t) → ℝ)}
    (hA : Assumption32 D P ξ Ξ) (𝒯 : ScenarioTree D Ξ) (root : 𝒯.Node 1)
    (z : ∀ τ, Fin (D.n τ) → ℝ) :
    qFn 𝒯 P ξ 1 root z = aggValue 𝒯 P ξ := by sorry

end KallMayerSLP.Multistage
