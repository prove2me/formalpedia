-- Prove2me | Theorems.Thm_Mazoit2013_leaf_normalization
-- name    : Mazoit2013.leaf_normalization
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-14T01:20:58.640204+00:00
-- url     : https://prove2.me/theorems/06444fb8-06fc-444e-94a6-da9575ed5f71
-- title:
--   Normalize a partial-decomposition leaf to its flap and boundary
-- statement:
--   In a finite graph, let a partial tree decomposition have bag threshold b and a large leaf t attached to u. Write X for its flap, the vertices in the leaf bag but not the attachment bag. Replacing that leaf bag by X together with its external graph boundary preserves the partial decomposition at threshold b. It creates no new flaps and preserves every flap other than X. If the replacement bag is small, X disappears. The boundary and replacement are explicitly constructed; no gluing or separator-minimality hypothesis is assumed.
-- source:
--   Mazoit, A simple proof of the tree-width duality theorem, https://arxiv.org/pdf/1309.2266, p. 2, partial decompositions and the preparation for Lemma 1. Explicit normalization lemma for this formalization.

import Definitions.Def_Mazoit2013_PartialDecompositions
open RobertsonSeymour1986.GM5 StableMSR.Recovery.Havens StableMSR.Recovery.PartialDecompositions

theorem Mazoit2013.leaf_normalization {V T : Type} [Fintype V] [DecidableEq V] [DecidableEq T]
    {G : SimpleGraph V} {b : ℕ} {tree : SimpleGraph T} {bags : T → Finset V}
    (h : IsPartial G b tree bags) {t u : T} (hbig : b < (bags t).card)
    (htu : tree.Adj t u) :
    ∃ B : Finset V,
      (∀ y, y ∈ B ↔ y ∈ bags t \ bags u ∨
        (y ∉ bags t \ bags u ∧ ∃ x ∈ bags t \ bags u, G.Adj x y)) ∧
      B ⊆ bags t ∧
      IsPartial G b tree (Function.update bags t B) ∧
      flaps b tree (Function.update bags t B) ⊆ flaps b tree bags ∧
      (∀ C ∈ flaps b tree bags, C ≠ bags t \ bags u →
        C ∈ flaps b tree (Function.update bags t B)) ∧
      (B.card ≤ b → bags t \ bags u ∉ flaps b tree (Function.update bags t B)) := by sorry
