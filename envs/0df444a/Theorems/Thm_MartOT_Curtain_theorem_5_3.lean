-- Prove2me | Theorems.Thm_MartOT_Curtain_theorem_5_3
-- name    : MartOT.Curtain.theorem_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:20:26.162339+00:00
-- url     : https://prove2.me/theorems/b01ab23d-2a58-4fe1-a3f8-f3b94ca49562
-- title:
--   Theorem 5.3, p. 33 — a left-monotone martingale transport plan is the left-curtain coupling of its marginals
-- statement:
--   Let $\mu,\nu$ be finite Borel measures on $\mathbb R$ with finite first moments, and let $\pi$ be a martingale transport plan with marginals $\mu=\operatorname{proj}^x_\#\pi$ and $\nu=\operatorname{proj}^y_\#\pi$ that is left-monotone (Definition 1.4). Then $\pi$ is the left-curtain coupling from $\mu$ to $\nu$: for every $x\in\mathbb R$,
--
--   $$\operatorname{proj}^x_\#\big(\pi|_{]-\infty,x]\times\mathbb R}\big)=\mu|_{]-\infty,x]},\qquad\operatorname{proj}^y_\#\big(\pi|_{]-\infty,x]\times\mathbb R}\big)=S^\nu(\mu|_{]-\infty,x]}).$$
--
--   This is the uniqueness half of Theorem 1.5: a left-monotone martingale plan is determined by its marginals.
--
--   **Formalization Note** Section 5 works with finite measures of any mass, so $\mu,\nu$ are taken in $\mathcal M$ rather than probability measures; this contains the probability case. No convex-order hypothesis is added: $\mu\preceq_C\nu$ follows from the existence of the martingale plan $\pi$. The conclusion is the defining property `IsLeftCurtain μ ν π` of Theorem 4.18, with $S^\nu(\cdot)$ the shadow predicate.
-- source:
--   arXiv:1208.1509v2, Theorem 5.3, p. 33 (proof pp. 33–35)

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Curtain

open MeasureTheory

theorem theorem_5_3 (μ ν : Measure ℝ) (hμ : MartOT.Var.InM μ) (hν : MartOT.Var.InM ν) (π : Measure (ℝ × ℝ))
    (hπ : MartOT.Var.IsMartingalePlan μ ν π) (hmono : MartOT.Var.IsLeftMonotone π) :
    MartOT.Var.IsLeftCurtain μ ν π := by sorry

end MartOT.Curtain
