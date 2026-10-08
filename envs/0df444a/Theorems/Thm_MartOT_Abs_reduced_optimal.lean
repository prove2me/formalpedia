-- Prove2me | Theorems.Thm_MartOT_Abs_reduced_optimal
-- name    : MartOT.Abs.reduced_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:20:01.367416+00:00
-- url     : https://prove2.me/theorems/3e67ce43-59a0-4d61-b5b5-c6859e104471
-- title:
--   Proof of Theorem 7.4, p. 46 — π − (Id ⊗ Id)_#(µ ∧ ν) is optimal between µ − µ ∧ ν and ν − µ ∧ ν, and these have µ̄ ∧ ν̄ = 0
-- statement:
--   Let $\mu,\nu$ be probability measures on $\mathbb R$ in convex order and let $\pi$ be an optimal martingale transport plan for $c(x,y)=|y-x|$. Put
--
--   $$\bar\mu=\mu-\mu\wedge\nu,\qquad\bar\nu=\nu-\mu\wedge\nu,\qquad\bar\pi=\pi-(\mathrm{Id}\otimes\mathrm{Id})_\#(\mu\wedge\nu).$$
--
--   Then $\bar\pi$ is an optimal martingale transport plan between the finite measures $\bar\mu$ and $\bar\nu$ for the same cost, and $\bar\mu\wedge\bar\nu=0$.
--
--   This reduces the uniqueness question of Theorem 7.4 to marginals that share no mass, where every optimal plan is concentrated on two graphs and Lemma 5.6 applies.
--
--   **Formalization Note** $\bar\mu,\bar\nu$ are finite measures of total mass $1-(\mu\wedge\nu)(\mathbb R)$, not probability measures; martingale plans and optimality between them are those of the Setting layer, which are defined for arbitrary measures (Section 2.1 of the paper). Subtraction of measures is Mathlib's truncated subtraction, which is exact here because $\mu\wedge\nu\le\mu$, $\mu\wedge\nu\le\nu$, and, by the previous step, $(\mathrm{Id}\otimes\mathrm{Id})_\#(\mu\wedge\nu)\le\pi$.
-- source:
--   arXiv:1208.1509v2, proof of Theorem 7.4, p. 46 (last paragraph)

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Abs

open MeasureTheory

theorem reduced_optimal (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : MartOT.Var.ConvexLE μ ν) (π : Measure (ℝ × ℝ)) (hπ : MartOT.Var.IsOptimal (fun x y => |y - x|) μ ν π) :
    MartOT.Var.IsOptimal (fun x y => |y - x|) (μ - μ ⊓ ν) (ν - μ ⊓ ν)
        (π - (μ ⊓ ν).map (fun x : ℝ => (x, x))) ∧
      (μ - μ ⊓ ν) ⊓ (ν - μ ⊓ ν) = 0 := by sorry

end MartOT.Abs
