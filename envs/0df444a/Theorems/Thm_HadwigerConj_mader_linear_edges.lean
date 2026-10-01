-- Prove2me | Theorems.Thm_HadwigerConj_mader_linear_edges
-- name    : HadwigerConj.mader_linear_edges
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T23:45:34.685527+00:00
-- url     : https://prove2.me/theorems/d370bfbb-f40d-43a7-a36e-3345482d9998
-- title:
--   Theorem 3.2 (Mader 1967): excluding any fixed minor forces linearly many edges
-- statement:
--   For every finite graph $H$ there is a constant $c$ such that every finite graph $G$ with no $H$ minor satisfies
--
--   $$|E(G)|\le c\,|V(G)|.$$
--
--   Consequently graphs excluding a fixed minor have bounded degeneracy and bounded chromatic number.
--
--   **Formalization Note** The constant is taken to be a natural number, which is no loss of generality.
-- source:
--   P. Seymour, "Hadwiger's conjecture" (survey), in: Open Problems in Mathematics, Springer, 2016 (uploaded PDF `paper.pdf`), Theorem 3.2 (p. 4)

import Mathlib
import Definitions.Def_HadwigerConj_Defs

namespace HadwigerConj
theorem mader_linear_edges {W : Type} [Finite W] (H : SimpleGraph W) :
    ∃ c : ℕ, ∀ (V : Type) [Finite V] (G : SimpleGraph V),
      ¬ IsMinor H G → G.edgeSet.ncard ≤ c * Nat.card V := by sorry
end HadwigerConj
