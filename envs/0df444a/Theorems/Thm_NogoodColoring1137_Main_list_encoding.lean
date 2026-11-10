-- Prove2me | Theorems.Thm_NogoodColoring1137_Main_list_encoding
-- name    : NogoodColoring1137.Main.list_encoding
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T17:02:39.69208+00:00
-- url     : https://prove2.me/theorems/705ce982-8772-4805-a349-f3f35664f430
-- title:
--   Lemma 7.1 — Same-vertex-set list encoding and factor six
-- statement:
--   Let $G$ have diameter at most two, all lists be nonempty, and distinct existing anchors satisfy $L(r_\alpha)=\{\alpha\}$. Add their triangle and the forbidden-color edges to obtain $G'$ on the same vertex set. Then
--   $$\mathcal C(G')\ne\varnothing\iff\mathcal C(G,L)\ne\varnothing,\qquad |\mathcal C(G')|=6|\mathcal C(G,L)|.$$
--   The graph retains diameter at most two. A uniform polynomial-time constructor outputs this graph, and another uniform polynomial-time program converts every proper coloring of it by a color permutation to a proper list coloring normalized at the anchors.
--
--   This supplies all clauses of the anchor reduction. **Formalization Note** The anchors are input vertices. Anchor existence is not imposed on the goal or Theorem 4; fixed color names explain the exact factor six.
--
--   Differences from the source:
--   - encoding: deterministic algorithms on explicit finite inputs → actual finite multitape bit-machine runs with binary integer and explicit output encodings; reason: the source fixes no bit layout; uniform programs and positive constants precede every input
-- source:
--   Philip Whittington, STOC 2027 submission #1137 (October 2026), Lemma 7.1, p.21

import Definitions.Def_NogoodColoring1137_Main_Computation

namespace NogoodColoring1137.Main

/-- Lemma 7.1, p.21: the specified same-vertex-set graph, conversion, iff and factor six. -/
theorem list_encoding :
    ∃ (build normalize : IntMul.MultitapeTM) (c e : ℕ), 0 < c ∧
    ∀ n (G : SimpleGraph (Fin n)) (adj : DecidableRel G.Adj) (L : Lists n)
      (r : Color → Fin n),
      DiameterTwo G → (∀ v, (L v).Nonempty) → Function.Injective r →
      (∀ a, L (r a) = {a}) →
      let H := AnchorGraph G L r
      DiameterTwo H ∧
      ((Solutions H (FullLists n)).Nonempty ↔ (@Solutions n G adj L).Nonempty) ∧
      (Solutions H (FullLists n)).card = 6 * (@Solutions n G adj L).card ∧
      Runs build (@EncodeInstance n G adj L ++
        (List.finRange 3).flatMap (fun a => EncodeNat (r a).val)) (EncodeGraph H)
        (c * ((n : ℝ)+1)^e) ∧
      ∀ C ∈ Solutions H (FullLists n), ∃ D ∈ @Solutions n G adj L,
        (∃ perm : Equiv.Perm Color, ∀ v, D v = perm (C v)) ∧
        (∀ a, D (r a) = a) ∧
        Runs normalize (@EncodeInstance n G adj L ++
          (List.finRange 3).flatMap (fun a => EncodeNat (r a).val) ++ EncodeColoring C)
          (EncodeColoring D) (c * ((n : ℝ)+1)^e) := by sorry

end NogoodColoring1137.Main
