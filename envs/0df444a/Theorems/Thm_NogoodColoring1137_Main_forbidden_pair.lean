-- Prove2me | Theorems.Thm_NogoodColoring1137_Main_forbidden_pair
-- name    : NogoodColoring1137.Main.forbidden_pair
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T17:02:53.96221+00:00
-- url     : https://prove2.me/theorems/fa7ba890-1497-48d7-b505-5b6c797963e2
-- title:
--   Lemma 6.1 — Forbidden pairs after singleton propagation
-- statement:
--   Let $G$ have diameter at most two and nonempty lists of size at most two from the common palette, after singleton propagation has finished. For vertices $v,w$ with different two-lists, a uniform polynomial-time program finds $\alpha\in L(v)$ and $\beta\in L(w)$ such that
--   $$\nexists C\in\mathcal C(G,L),\quad C(v)=\alpha\land C(w)=\beta.$$
--   All vertices remain present and singleton neighbor colors are excluded. Pair existence and computation are conclusions. This supplies the counting recursion's branching certificates.
--
--   **Formalization Note** Program and polynomial constants precede every graph, list and queried vertex pair. Empty lists are excluded here exactly as in the source.
--
--   Differences from the source:
--   - encoding: deterministic algorithms on explicit finite inputs → actual finite multitape bit-machine runs with binary integer and explicit output encodings; reason: the source fixes no bit layout; uniform programs and positive constants precede every input
-- source:
--   Philip Whittington, STOC 2027 submission #1137 (October 2026), Lemma 6.1, pp.19–20

import Definitions.Def_NogoodColoring1137_Main_Computation

namespace NogoodColoring1137.Main

/-- Lemma 6.1, pp.19–20, including the algorithmic assertion. -/
theorem forbidden_pair :
    ∃ (P : IntMul.MultitapeTM) (c e : ℕ), 0 < c ∧
    ∀ n (G : SimpleGraph (Fin n)) (adj : DecidableRel G.Adj) (L : Lists n),
      DiameterTwo G → (∀ v, (L v).Nonempty ∧ (L v).card ≤ 2) → Propagated G L →
      ∀ v w, (L v).card = 2 → (L w).card = 2 → L v ≠ L w →
      ∃ a ∈ L v, ∃ b ∈ L w,
        (∀ C ∈ @Solutions n G adj L, ¬ (C v = a ∧ C w = b)) ∧
        Runs P (@EncodeInstance n G adj L ++ EncodeNat v.val ++ EncodeNat w.val)
          (IntMul.bin 2 a.val ++ IntMul.bin 2 b.val) (c * ((n : ℝ)+1)^e) := by sorry

end NogoodColoring1137.Main
