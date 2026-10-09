-- Prove2me | Theorems.Thm_GraphonGames_Stability_proposition_3_1_aggregate_exists_unique
-- name    : GraphonGames.Stability.proposition_3_1_aggregate_exists_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T17:45:08.274398+00:00
-- url     : https://prove2.me/theorems/340d096a-6310-4918-812e-b054e16a263b
-- title:
--   Proposition 3.1 — existence and uniqueness of the aggregate
-- statement:
--   Let $w$ be a real, symmetric, square-integrable graphon with integral operator $W$. Suppose the state map $b$ and centered noise law satisfy Assumption 1 with constants $c_\alpha,c_z\geq0$, and $\sqrt{c_z}\|W\|<1$. For every $L^2$ strategy profile $\alpha$, there is an $L^2$ aggregate $z$ satisfying
--
--   $$
--   z(x)=\int_I w(x,y)b(\alpha(y),z(y))\,dy\quad\text{for almost every }x\in I,
--   $$
--
--   and every other such aggregate equals $z$ almost everywhere.
--
--   This defines the aggregate operator used throughout the graphon game.
--
--   **Formalization Note** Uniqueness is of $L^2$ equivalence classes, so it is stated as almost-everywhere equality. The centered noise law is part of the standing Assumption 1 representation.
-- source:
--   Carmona, Cooney, Graves & Laurière, Stochastic Graphon Games: I. The Static Case, arXiv:1911.10664v1, p. 8, Proposition 3.1 and (6)

import Mathlib
import Definitions.Def_GraphonGames_Stability_Setting

open MeasureTheory

namespace GraphonGames.Stability

theorem proposition_3_1_aggregate_exists_unique
    (b : ℝ → ℝ → ℝ) (μ0 : Measure ℝ) (cα cz : ℝ)
    (h1 : GraphonGames.Existence.Asm1 b μ0 cα cz)
    (w : I → I → ℝ) (hw : IsGraphon w)
    (hW : Real.sqrt cz * (opNorm w).toReal < 1)
    (α : I → ℝ) (hα : MemLp α 2 volume) :
    ∃ z, IsAggregate w b α z ∧
      ∀ z', IsAggregate w b α z' → z' =ᵐ[volume] z := by sorry

end GraphonGames.Stability
