-- Prove2me | Theorems.Thm_KallMayerSLP_Multistage_eq_3_15_value
-- name    : KallMayerSLP.Multistage.eq_3_15_value
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:19:29.122956+00:00
-- url     : https://prove2.me/theorems/1ca63e9e-46e8-4747-91d6-6c725ed8826b
-- title:
--   (3.15) — the recursion computes the optimal value of (3.10)
-- statement:
--   Let (3.10) satisfy Assumption 3.2. With $\Phi_{T+1}\equiv0$ and, for $t=T,\dots,2$,
--   $$
--   r_t(z_{t-1};\widehat\zeta_t)=\min_{x_t}\{c_t^{\mathsf T}x_t+\Phi_{t+1}(z_t;\widehat\zeta_t)\}\ \text{ s.t. }\ A_{tt}x_t=b_t(\widehat\zeta_t)-\sum_{\tau=1}^{t-1}A_{t\tau}x_\tau,\ x_t\ge0,
--   $$
--   $$
--   \Phi_t(z_{t-1};\widehat\zeta_{t-1})=\mathbb E_{\xi_t}\big[r_t(z_{t-1};\widehat\zeta_{t-1},\xi_t)\big],
--   $$
--   the final value
--   $$
--   r_1=\min_{x_1}\{c_1^{\mathsf T}x_1+\Phi_2(x_1;\widehat\zeta_1)\}\ \text{ s.t. }\ A_{11}x_1=b_1,\ x_1\ge0
--   $$
--   is the optimal value of (3.10).
--
--   The book quotes this equivalence from Olsen and from Rockafellar and Wets. It reduces the problem over decision functions to a sequence of finite-dimensional problems.
--
--   **Formalization Note** The optimal value is the infimum over measurable square-integrable policies, so this is a theorem and not a definition. Both sides are extended reals.
--
--   Differences from the source:
--   - reading: Assumption 3.2: the A_tt complete fixed recourse matrices ∀t → complete recourse of A_tt for t = 2, …, T; reason: A_11 is not a recourse matrix, and the book's Example 3.1 calls a problem with a non-complete first stage complete fixed recourse; this is the weaker hypothesis, so the statement implies the ∀t one
--   - generalization: supp ℙ_{ξ_t} ⊆ Ξ^t → ξ_t ∈ Ξ^t almost surely; reason: the support inclusion implies the almost sure one, and they agree for closed Ξ^t, so the statement specializes to the source
--   - encoding: min → infimum in EReal; reason: +∞ on infeasible and -∞ on unbounded problems; the book assumes neither case away
--   - encoding: z_{t-1} and ζ̂_t as finite sequences → full families z and w, of which only the coordinates the book lists are used; reason: the same functions; unused coordinates have no effect
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, (3.15) and the display after it, pp.263–264 (PDF 272–273)

import Mathlib
import Definitions.Def_KallMayerSLP_Multistage_Assumption32
import Definitions.Def_KallMayerSLP_Multistage_value
import Definitions.Def_KallMayerSLP_Multistage_rFn

namespace KallMayerSLP.Multistage

open MeasureTheory

/-- **Chapter 3, (3.15): the recursion computes the optimal value of (3.10)** (Kall & Mayer,
*Stochastic Linear Programming* (2005), Chapter 3, p.263, PDF 272 – p.264, PDF 273): the recursion
(3.15) "finally yields `r_1 = min_{x_1} {c_1ᵀ x_1 + Φ_2(x_1; ζ̂_1)}` s.t. `A_11 x_1 = b_1(ζ̂_1) ≡ b_1`,
`x_1 ≥ 0`, the optimal value of (3.10)".

**Formalization Note.** `value` is the infimum over measurable square-integrable policies, so this
is the equivalence the book quotes from Olsen and Rockafellar–Wets, not a definition. `r_1` does not
depend on `z` or `w`, which are universally quantified. Both sides are in `EReal`. -/
theorem eq_3_15_value {D : MSLP} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ξ : ∀ t, Ω → Fin (D.r t) → ℝ} {Ξ : ∀ t, Set (Fin (D.r t) → ℝ)}
    (hA : Assumption32 D P ξ Ξ) (z : ∀ τ, Fin (D.n τ) → ℝ) (w : ∀ s, Fin (D.r s) → ℝ) :
    rFn D (fun t => P.map (ξ t)) 1 z w = value D P ξ := by sorry

end KallMayerSLP.Multistage
