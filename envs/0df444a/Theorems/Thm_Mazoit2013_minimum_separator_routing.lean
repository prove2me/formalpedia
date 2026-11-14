-- Prove2me | Theorems.Thm_Mazoit2013_minimum_separator_routing
-- name    : Mazoit2013.minimum_separator_routing
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-14T01:21:43.297564+00:00
-- url     : https://prove2.me/theorems/12709017-1833-464e-97f0-769e7bf1fd0f
-- title:
--   Restrict a partial decomposition through a minimum separator without increasing bags
-- statement:
--   Let a graph have a partial tree decomposition at threshold b, rooted at a leaf. Let S be a minimum-cardinality separator between the root bag and a target set, and B a retained side containing S and the target. Assume the root bag meets B only inside S, every edge entering B enters through S, and S has size at most b. There is a partial decomposition of the graph induced by B on the same tree, with root bag exactly S and every bag no larger than before. Every resulting flap is contained in an original flap other than the selected root flap. The construction routes separator vertices along tree paths; its size bound follows directly from separator minimality, without a vertex-disjoint-paths theorem. This is the complete one-side modification used in partial-decomposition gluing.
-- source:
--   Seymour and Thomas, Graph Searching and a Min-Max Theorem for Tree-Width, https://thomas.math.gatech.edu/PAP/search.pdf, Lemma 2.4; Mazoit arXiv:1309.2266, p.2 Lemma 1. Direct minimum-separator proof of the routed restriction step.

import Definitions.Def_Mazoit2013_PartialDecompositions
open RobertsonSeymour1986.GM5 StableMSR.Recovery.PartialDecompositions

theorem Mazoit2013.minimum_separator_routing {V T : Type} [Fintype V] [DecidableEq V] [DecidableEq T]
    {G : SimpleGraph V} {tree : SimpleGraph T} {bags : T → Finset V} {b : ℕ}
    (h : IsPartial G b tree bags) (B S target : Finset V) (root u : T)
    (hSb : S.card ≤ b) (hSB : S ⊆ B) (htarget : target ⊆ B)
    (hroot : bags root ∩ B ⊆ S) (hleaf : ∀ z, tree.Adj root z → z = u)
    (hboundary : ∀ x, x ∉ B → ∀ y, G.Adj x y → y ∈ B → y ∈ S)
    (hmin : ∀ D : Finset V,
      (∀ x ∈ bags root, ∀ y ∈ target, ∀ p : G.Walk x y, ∃ z ∈ p.support, z ∈ D) →
      S.card ≤ D.card) :
    ∃ newbags : T → Finset V,
      newbags root = S ∧ (∀ t, newbags t ⊆ B) ∧
      (∀ t, (newbags t).card ≤ (bags t).card) ∧
      IsPartial (G.induce (B : Set V)) b tree (fun t => (newbags t).subtype (· ∈ B)) ∧
      ∀ C ∈ flaps b tree newbags,
        ∃ A ∈ flaps b tree bags, A ≠ bags root \ bags u ∧ C ⊆ A := by sorry
