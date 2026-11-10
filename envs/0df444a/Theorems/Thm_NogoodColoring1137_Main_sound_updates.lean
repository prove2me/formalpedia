-- Prove2me | Theorems.Thm_NogoodColoring1137_Main_sound_updates
-- name    : NogoodColoring1137.Main.sound_updates
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T17:01:24.931906+00:00
-- url     : https://prove2.me/theorems/199f8fab-68ea-4326-8de2-d46c8f05e913
-- title:
--   Lemma 4.1 — Sound projection and exact slicing
-- statement:
--   Let $1\le\ell\le n$, let every domain have at least two labels, and let $W$ be a valid table on active coordinates $U$. If $W$ is sound for a code $Q$, every active coordinate $v$ and label $b$ satisfy
--   $$\Pi_vW\text{ sound for }\Pi_vQ,\qquad W_v^b\text{ sound for }Q_v^b.$$
--   Independently of soundness, if all active $\ell$-scopes are certified, every remaining $\ell$-scope is certified after either update. Old certificates have priority in slicing. This maintains replay soundness.
--
--   **Formalization Note** TableValid expresses the source definition of a table. Empty codes and empty scopes remain allowed.
--
--   Differences from the source:
--   - encoding: finite coordinates and heterogeneous finite domains → Fin n and Fin (d v), with dependent words on scopes; reason: independent bijective relabeling preserves all words, certificates, boxes and counts
-- source:
--   Philip Whittington, STOC 2027 submission #1137 (October 2026), Lemma 4.1, p.11

import Definitions.Def_NogoodColoring1137_Main_Codes

namespace NogoodColoring1137.Main

/-- Lemma 4.1, p.11. -/
theorem sound_updates {n : ℕ} (d : Fin n → ℕ) (hd : ∀ v, 2 ≤ d v)
    (ell : ℕ) (hell : 1 ≤ ell ∧ ell ≤ n)
    (U : Finset (Fin n)) (Q : Code d U) (W : Table d) (v : U)
    (hvalid : TableValid ell U W) :
    (Sound Q W → Sound (ProjectCode v.val Q) (ProjectTable v.val W) ∧
      ∀ b : Fin (d v.val), Sound (SliceCode v b Q) (SliceTable v.val b W)) ∧
    (CompleteAt ell U W → CompleteAt ell (U.erase v.val) (ProjectTable v.val W) ∧
      ∀ b : Fin (d v.val), CompleteAt ell (U.erase v.val) (SliceTable v.val b W)) := by sorry

end NogoodColoring1137.Main
