-- Prove2me | Theorems.Thm_LiuHelsenDesigns_OneD_lemma_13
-- name    : LiuHelsenDesigns.OneD.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T11:06:25.864025+00:00
-- url     : https://prove2.me/theorems/81e95dd2-be1e-486d-9ac4-033af98af997
-- title:
--   Lemma 13 — elementary groups over matrix rings
-- statement:
--   Let R be any unital ring, possibly noncommutative, and let $n,m\ge2$. Under actual block-matrix flattening,
--
--   $$
--   EL(n;\operatorname{Mat}(m;R))=EL(nm;R).
--   $$
--
--   The block coordinates are pairs of indices; flattening preserves every matrix entry and does not replace R by a field.
--
--   Differences from the source:
--   - encoding: nm flattened coordinates → the pair index Fin n × Fin m; reason: canonical block identification has exactly nm entries and keeps every matrix entry
-- source:
--   Guoding Liu, Jonas Helsen, STOC 2027 submission #221 (October 2026), p. 32, Lemma 13. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/221.pdf

import Definitions.Def_LiuHelsenDesigns_OneD_elementary

namespace LiuHelsenDesigns.OneD
theorem lemma_13 (R : Type) [Ring R] (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (A : Matrix (Fin n) (Fin n) (Matrix (Fin m) (Fin m) R)) :
    A ∈ EL (Fin n) (Matrix (Fin m) (Fin m) R) ↔
      flattenBlocks A ∈ EL (Fin n × Fin m) R := by sorry
end LiuHelsenDesigns.OneD
