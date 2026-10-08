-- Prove2me | Theorems.Thm_MartOT_Product_plan_determined_by_targets
-- name    : MartOT.Product.plan_determined_by_targets
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:21:11.069631+00:00
-- url     : https://prove2.me/theorems/14998329-66f2-4f20-b5cb-53974d7ca8d6
-- title:
--   §1.3, p. 7 — a transport plan π ∈ Π(µ,ν) is uniquely determined by the family (ν^π_t)_{t∈ℝ}
-- statement:
--   Let $\mu$ be a finite Borel measure on $\mathbb R$ and $\nu$ a Borel measure on $\mathbb R$. For a transport plan $\pi\in\Pi(\mu,\nu)$ and $t\in\mathbb R$ let
--
--   $$\nu^\pi_t=\mathrm{proj}^y_\#\big(\pi|_{(-\infty,t]\times\mathbb R}\big),$$
--
--   the image under $\pi$ of the mass $\mu|_{(-\infty,t]}$. If $\pi,\pi'\in\Pi(\mu,\nu)$ satisfy $\nu^\pi_t=\nu^{\pi'}_t$ for every $t\in\mathbb R$, then $\pi=\pi'$.
--
--   This is the observation that lets the left-curtain coupling be defined through its targets $\nu^{\pi_{lc}}_t=S^\nu(\mu|_{(-\infty,t]})$, and it is the last step of the proof of Theorem 6.3: an optimal plan with the same targets as $\pi_{lc}$ is $\pi_{lc}$.
--
--   **Formalization Note** The page says "it is intuitively clear (and not hard to verify)"; it is stated here for a finite $\mu$, the setting of every use in the paper.
-- source:
--   arXiv:1208.1509v2, §1.3, p. 7

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Product

open MeasureTheory

/-- §1.3 (p. 7): a transport plan `π ∈ Π(μ, ν)` is uniquely determined by the family
`(ν^π_t)_{t ∈ ℝ}`. -/
theorem plan_determined_by_targets (μ ν : Measure ℝ) [IsFiniteMeasure μ]
    (π π' : Measure (ℝ × ℝ)) (hπ : MartOT.Var.IsPlan μ ν π) (hπ' : MartOT.Var.IsPlan μ ν π')
    (h : ∀ t : ℝ, MartOT.Var.targetUpTo π t = MartOT.Var.targetUpTo π' t) :
    π = π' := by sorry

end MartOT.Product
