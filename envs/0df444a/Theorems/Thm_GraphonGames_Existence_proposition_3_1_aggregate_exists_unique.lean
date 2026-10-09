-- Prove2me | Theorems.Thm_GraphonGames_Existence_proposition_3_1_aggregate_exists_unique
-- name    : GraphonGames.Existence.proposition_3_1_aggregate_exists_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:54:53.921959+00:00
-- url     : https://prove2.me/theorems/a0897e40-33a9-4d61-9a09-92c6974ec5ca
-- title:
--   Proposition 3.1, p. 8 — under √c_z‖W‖ < 1 each α ∈ L²(I) has a unique aggregate z solving (6)
-- statement:
--   Let $w$ be a graphon with integral operator $\mathbf W$, and let the state map $b$ and noise law $\mu_0$ satisfy Assumption 1 with constants $c_\alpha,c_z\ge0$. Assume $\sqrt{c_z}\|\mathbf W\|<1$. Then for every profile $\alpha\in L^2(I)$ there is a $z\in L^2(I)$ with
--   $$z_x=\int_I w(x,y)\,b(\alpha_y,z_y)\,dy\qquad\text{for }\lambda_I\text{-a.e. }x\in I,$$
--   and any other $z'\in L^2(I)$ with this property agrees with $z$ almost everywhere.
--
--   This defines the aggregate map $\alpha\mapsto\mathbf Z\alpha$ on $L^2(I)$, which every later statement presupposes.
--
--   **Formalization Note.** Uniqueness is up to $\lambda_I$-a.e. equality, the equality of $L^2(I)$.
-- source:
--   Carmona, Cooney, Graves & Laurière, Stochastic Graphon Games: I. The Static Case, arXiv:1911.10664v1, p. 8, Proposition 3.1, (6)

import Mathlib
import Definitions.Def_GraphonGames_Existence_Setting

open MeasureTheory
open scoped ENNReal

namespace GraphonGames.Existence

theorem proposition_3_1_aggregate_exists_unique (b : ℝ → ℝ → ℝ) (μ0 : Measure ℝ) (cα cz : ℝ)
    (h1 : Asm1 b μ0 cα cz) (w : I → I → ℝ) (hw : IsGraphon w)
    (hW : Real.sqrt cz * (opNorm w).toReal < 1) (α : I → ℝ) (hα : MemLp α 2 volume) :
    ∃ z : I → ℝ, IsAggregate w b α z ∧ ∀ z' : I → ℝ, IsAggregate w b α z' → z' =ᵐ[volume] z := by sorry

end GraphonGames.Existence
