-- Prove2me | Theorems.Thm_JHolomorphic_HasWeakPartialsOn_univ_of_support_subset_closedBall
-- name    : JHolomorphic.HasWeakPartialsOn.univ_of_support_subset_closedBall
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T21:15:26.851019+00:00
-- url     : https://prove2.me/theorems/cf86dd20-bf5c-445d-b0e4-fb8fbd014658
-- title:
--   Weak partial derivatives supported in a disc compactly inside $U$ are weak partial derivatives on $\mathbb{C}$
-- statement:
--   Let $E$ be a real normed space, $U\subseteq\mathbb{C}$, $c\in\mathbb{C}$ and $0<R<R'$ with $\bar B(c,R')\subseteq U$. Let $u,u_s,u_t:\mathbb{C}\to E$ vanish outside $\bar B(c,R)$, and suppose $u_s,u_t$ are weak partial derivatives of $u$ on $U$ (`HasWeakPartialsOn U u uₛ uₜ`). Then $u_s,u_t$ are weak partial derivatives of $u$ on all of $\mathbb{C}$: the defining identities
--   $$\int_{\mathbb{C}}\bigl(D\varphi\,1\bigr)\,u=-\int_{\mathbb{C}}\varphi\,u_s,\qquad \int_{\mathbb{C}}\bigl(D\varphi\,i\bigr)\,u=-\int_{\mathbb{C}}\varphi\,u_t$$
--   hold for every real $C^\infty$ function $\varphi$ with compact support, with no condition on its support. This lets maps supported well inside $U$ be treated as maps on the whole plane.
--
--   **Formalization Note** "Vanish outside $\bar B(c,R)$" is `Function.support _ ⊆ closedBall c R`; the conclusion is `HasWeakPartialsOn Set.univ u uₛ uₜ`. No integrability hypotheses are needed.
-- source:
--   Standard; cf. L. C. Evans, Partial Differential Equations, §5.2.1

import Definitions.Def_JHolomorphic_Setting

namespace JHolomorphic

open MeasureTheory Metric
open scoped ContDiff

/-- If `uₛ`, `uₜ` are weak partial derivatives of `u` on `U`, and `u`, `uₛ`, `uₜ` all vanish
outside a closed disc `B̄(c, R)` whose concentric enlargement `B̄(c, R')`, `R < R'`, lies in `U`,
then `uₛ`, `uₜ` are weak partial derivatives of `u` on all of `ℂ`. -/
theorem HasWeakPartialsOn.univ_of_support_subset_closedBall {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Set ℂ} {c : ℂ} {R R' : ℝ} (hR : 0 < R)
    (hRR' : R < R') (hU : closedBall c R' ⊆ U) {f fs ft : ℂ → E}
    (h : HasWeakPartialsOn U f fs ft) (hf : Function.support f ⊆ closedBall c R)
    (hfs : Function.support fs ⊆ closedBall c R) (hft : Function.support ft ⊆ closedBall c R) :
    HasWeakPartialsOn Set.univ f fs ft := by
  sorry

end JHolomorphic
