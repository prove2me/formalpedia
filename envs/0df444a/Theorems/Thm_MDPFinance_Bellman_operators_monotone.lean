-- Prove2me | Theorems.Thm_MDPFinance_Bellman_operators_monotone
-- name    : MDPFinance.Bellman.operators_monotone
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T20:12:19.105909+00:00
-- url     : https://prove2.me/theorems/727f81e8-85ae-483b-a9f7-148e2dce8916
-- title:
--   Lemma 2.3.3 — monotonicity of $L_n$, $T_n^f$, $T_n$
-- statement:
--   The three operators of Definition 2.3.1 are monotone in $v$: if $v, w \in \mathrm{IM}(E)$ satisfy
--   $v(x) \le w(x)$ for every state $x$, then
--
--   $$
--   L_n v(x,a) \le L_n w(x,a) \ \text{ for all } (x,a) \in D_n, \qquad
--   T_n^f v(x) \le T_n^f w(x) \ \text{ for all } x \in E,\ f \in F_n, \qquad
--   T_n v(x) \le T_n w(x) \ \text{ for all } x \in E.
--   $$
--
--   The proof is immediate from monotonicity of the integral $\int v\, dQ_n(\cdot \mid x,a)$ in $v$,
--   which propagates first to $L_n$, then to $T_n^f$ (a special case of $L_n$), and finally to $T_n$
--   (a supremum of monotone quantities). Despite its short proof, this monotonicity is used
--   throughout the chapter's central arguments — most visibly inside the induction step of the
--   Structure Theorem (Theorem 2.3.8), where it licenses comparing $T_n$ applied to the true value
--   function against $T_n$ applied to the value of an arbitrary fixed policy.
--
--   **Formalization Note.** Stated as one theorem with the three inequalities as a conjunction,
--   mirroring the book's own a)/b)/c) structure; `T_n^f v \le T_n^f w` is stated for every decision
--   rule `f : E → A`, not only those in $F_n$, since the operator `Tf` is defined and monotone for
--   an arbitrary measurable `f`, and the extra generality costs nothing.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 20, Lemma 2.3.3

import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_MDPFinance_Bellman_Operators

open MeasureTheory ProbabilityTheory MDPFinance.Bellman

namespace MDPFinance.Bellman

/-- Lemma 2.3.3 (Bäuerle–Rieder, p. 20, PDF 35): all three operators `L_n`, `T_n^f`, `T_n` are
monotone: for `v, w ∈ IM(E)` with `v(x) ≤ w(x)` for all `x ∈ E` it holds that `L_n v ≤ L_n w` on
`D_n`, `T_n^f v ≤ T_n^f w` for every decision rule `f`, and `T_n v ≤ T_n w`. -/
theorem operators_monotone {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (n : ℕ) (v w : E → EReal) (hv : v ∈ IM E) (hw : w ∈ IM E)
    (hvw : ∀ x, v x ≤ w x) :
    (∀ xa ∈ M.D n, L M n v xa ≤ L M n w xa) ∧
    (∀ f : E → A, ∀ x, Tf M n v f x ≤ Tf M n w f x) ∧
    (∀ x, T M n v x ≤ T M n w x) := by sorry

end MDPFinance.Bellman
