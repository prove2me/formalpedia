-- Prove2me | Theorems.Thm_GavrilSubtree_Chordal_exists_isSimplicial
-- name    : GavrilSubtree.Chordal.exists_isSimplicial
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:53:58.215393+00:00
-- url     : https://prove2.me/theorems/44e257a1-d549-4962-aae5-0fd9909b7dd3
-- title:
--   Dirac–Rose, §1, p. 48 (cited) — every nonempty finite chordal graph has a simplicial vertex
-- statement:
--   Let $G$ be a finite chordal graph with at least one vertex. Then $G$ has a *simplicial vertex*: a vertex $v$ whose set of neighbours $\Gamma v$ is completely connected,
--   $$\exists v \in V : \ \Gamma v \text{ is a completely connected set of } G.$$
--
--   The paper cites this theorem of Dirac and Rose (references [14], [15]) in its introduction and uses it in the inductive step of the proof of Theorem 3.
--
--   **Formalization Note** The hypothesis that $V$ is nonempty is added: the statement "has a vertex" presupposes one, and it fails for the empty graph. The paper applies the theorem to a connected graph that is not complete, which is nonempty.
-- source:
--   Gavril, The intersection graphs of subtrees in trees are exactly the chordal graphs, J. Combin. Theory Ser. B 16 (1974), p. 48, §1 (theorem of Dirac [14] and Rose [15], cited)

import Mathlib
import Definitions.Def_GavrilSubtree_Chordal_Setting

namespace GavrilSubtree.Chordal

universe u

theorem exists_isSimplicial {V : Type u} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    (hG : IsChordal G) : ∃ v, IsSimplicial G v := by sorry

end GavrilSubtree.Chordal
