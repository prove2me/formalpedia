-- Prove2me | Theorems.Thm_KarimiPL_Rel_theorem_2
-- name    : KarimiPL.Rel.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-09T01:43:38.877624+00:00
-- url     : https://prove2.me/theorems/08868593-3548-4369-a1be-f4de1d63fce4
-- title:
--   Theorem 2, p. 3 — with a Lipschitz gradient, SC → ESC → WSC → RSI → EB ≡ PL → QG; for convex f, RSI ≡ EB ≡ PL ≡ QG
-- statement:
--   Let $f:\mathbb R^d\to\mathbb R$ be differentiable with an $L$-Lipschitz gradient, $\|\nabla f(x)-\nabla f(y)\|\le L\|x-y\|$ for all $x,y$, where $L>0$. Assume the solution set $\mathcal X^*$ of global minimizers is non-empty, let $x^*\in\mathcal X^*$ and $f^*=f(x^*)$, and let $x\mapsto x_p$ be a projection onto $\mathcal X^*$ ($x_p\in\mathcal X^*$ and $\|x-x_p\|=\operatorname{dist}(x,\mathcal X^*)$).
--
--   Say that a condition holds if it holds for some constant $\mu>0$; the constant may differ from condition to condition. For the conditions SC, ESC, WSC, RSI, EB, PL and QG of Appendix A (with $f^*$ as above in PL and QG), the following implications hold:
--   $$(SC)\to(ESC)\to(WSC)\to(RSI)\to(EB)\equiv(PL)\to(QG).$$
--   If moreover $f$ is convex, then
--   $$(RSI)\equiv(EB)\equiv(PL)\equiv(QG).$$
--   Here $\to$ is implication and $\equiv$ is equivalence.
--
--   The theorem shows that QG is the weakest of these conditions, and that PL and the equivalent EB are the most general ones among them that still guarantee linear convergence of gradient descent to a global minimizer; for convex functions the last four conditions coincide.
--
--   **Formalization Note** The conclusion is one conjunction of the six implications or equivalences of the first chain and, under `ConvexOn ℝ Set.univ f`, the three equivalences of the second. Each condition is read as "there is $\mu>0$ such that ..." (`Holds`), independently on each side of every arrow. PL is the published predicate `ShiOptRates.PolyakLojasiewicz f (gradient f) μ (f x*)` (the paper's (3) multiplied by 2). The projection is an explicit nearest-point selection `p` with `IsProjSel f p`; the theorem is stated for every such selection. Non-emptiness of $\mathcal X^*$ is the paper's standing assumption of §2 and is carried by the minimizer $x^*$.
-- source:
--   Karimi, Nutini, Schmidt, arXiv:1608.04636v4, Theorem 2, p. 3; conditions from Appendix A, pp. 11–12; standing assumptions §2, p. 2

import Mathlib
import Definitions.Def_ShiOptrates_FunctionClass
import Definitions.Def_KarimiPL_Rel_Conditions

namespace KarimiPL.Rel

theorem theorem_2 {d : ℕ} (f : E d → ℝ) (hdiff : Differentiable ℝ f)
    (L : ℝ) (hL : 0 < L) (hLip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (xstar : E d) (hxstar : ∀ y, f xstar ≤ f y)
    (p : E d → E d) (hp : IsProjSel f p) :
    (Holds (SC f) → Holds (ESC f p)) ∧
    (Holds (ESC f p) → Holds (WSC f p)) ∧
    (Holds (WSC f p) → Holds (RSI f p)) ∧
    (Holds (RSI f p) → Holds (EB f p)) ∧
    (Holds (EB f p) ↔ Holds (fun μ => ShiOptRates.PolyakLojasiewicz f (gradient f) μ (f xstar))) ∧
    (Holds (fun μ => ShiOptRates.PolyakLojasiewicz f (gradient f) μ (f xstar)) →
      Holds (QG f p (f xstar))) ∧
    (ConvexOn ℝ Set.univ f →
      (Holds (RSI f p) ↔ Holds (EB f p)) ∧
      (Holds (EB f p) ↔
        Holds (fun μ => ShiOptRates.PolyakLojasiewicz f (gradient f) μ (f xstar))) ∧
      (Holds (fun μ => ShiOptRates.PolyakLojasiewicz f (gradient f) μ (f xstar)) ↔
        Holds (QG f p (f xstar)))) := by sorry

end KarimiPL.Rel
