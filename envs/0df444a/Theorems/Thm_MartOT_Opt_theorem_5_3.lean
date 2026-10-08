-- Prove2me | Theorems.Thm_MartOT_Opt_theorem_5_3
-- name    : MartOT.Opt.theorem_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:19:46.009069+00:00
-- url     : https://prove2.me/theorems/5cdb6f50-c328-46b8-89ae-b9d022da6205
-- title:
--   Theorem 5.3, p. 33 — a monotone martingale transport plan is the left-curtain coupling of its marginals
-- statement:
--   Let $\pi$ be a finite measure on $\mathbb R\times\mathbb R$ whose marginals $\mu=\operatorname{proj}^x_\#\pi$ and $\nu=\operatorname{proj}^y_\#\pi$ have finite first moments. Assume that $\pi$ is a martingale transport plan from $\mu$ to $\nu$ and that $\pi$ is (left-)monotone (Definition 1.4). Then $\pi$ is the left-curtain coupling from $\mu$ to $\nu$: for every $x\in\mathbb R$,
--
--   $$\operatorname{proj}^x_\#\big(\pi|_{]-\infty,x]\times\mathbb R}\big)=\mu|_{]-\infty,x]},\qquad \operatorname{proj}^y_\#\big(\pi|_{]-\infty,x]\times\mathbb R}\big)=S^\nu\big(\mu|_{]-\infty,x]}\big).$$
--
--   Together with the uniqueness in Theorem 4.18, this says there is only one monotone martingale transport plan between two given marginals.
--
--   **Formalization Note** Section 5 works with finite measures with finite first moment ($\mathcal M$), not only probabilities; the statement is posed in that generality. The marginals' membership in $\mathcal M$ is stated explicitly.
-- source:
--   arXiv:1208.1509v2, Theorem 5.3, p. 33

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Opt

open MeasureTheory

theorem theorem_5_3 (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (hμ : MartOT.Var.InM (π.map Prod.fst)) (hν : MartOT.Var.InM (π.map Prod.snd))
    (hπ : MartOT.Var.IsMartingalePlan (π.map Prod.fst) (π.map Prod.snd) π) (hmono : MartOT.Var.IsLeftMonotone π) :
    MartOT.Var.IsLeftCurtain (π.map Prod.fst) (π.map Prod.snd) π := by sorry

end MartOT.Opt
