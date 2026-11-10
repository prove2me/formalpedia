-- Prove2me | Theorems.Thm_NogoodColoring1137_Main_connector_forcing
-- name    : NogoodColoring1137.Main.connector_forcing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T17:02:21.966064+00:00
-- url     : https://prove2.me/theorems/c5008381-b8a8-46cd-aca9-5fe0ea5406b4
-- title:
--   Lemma 5.1 — Connector Forcing
-- statement:
--   Let $q_1,\ldots,q_t$ be terminals, $z_1,\ldots,z_t$ a connector chain, and $C$ a proper extension of their assigned colors $c$. For $1\le i\le t$,
--   $$F_i(c)=a\implies C(z_i)=a.$$
--   Every occurrence of a repeated root satisfies the same assertion. Undefined folds impose no conclusion. This supplies forcing for the nogood construction.
--
--   **Formalization Note** A total vertex coloring represents the partial assignment; values away from the terminals are unused.
--
--   Differences from the source:
--   - generalization: the surrounding section assumes n ≥ 8 and diameter at most 2 → any finite graph with the specified connector; reason: the induction on pp.14–15 uses only connector edges and three colors
--   - encoding: a partial terminal assignment → a total assignment restricted by terminal equalities and bounded one-based indices; reason: any partial assignment extends arbitrarily to unused vertices
-- source:
--   Philip Whittington, STOC 2027 submission #1137 (October 2026), Lemma 5.1, pp.14–15

import Definitions.Def_NogoodColoring1137_Main_Folds

namespace NogoodColoring1137.Main

/-- Lemma 5.1, pp.14–15. Repeated physical roots remain repeated occurrences. -/
theorem connector_forcing {n t i : ℕ} (G : SimpleGraph (Fin n))
    (q z : ℕ → Fin n) (c : Fin n → Color) (C : Fin n → Color)
    (hchain : Connector G t q z) (hi : 1 ≤ i ∧ i ≤ t)
    (hproper : ∀ v w, G.Adj v w → C v ≠ C w)
    (hext : ∀ j, 1 ≤ j → j ≤ t → C (q j) = c (q j)) :
    ∀ a, FoldPrefix (fun j => c (q j)) i = some a → C (z i) = a := by sorry

end NogoodColoring1137.Main
