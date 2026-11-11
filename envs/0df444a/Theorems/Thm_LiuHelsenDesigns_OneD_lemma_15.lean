-- Prove2me | Theorems.Thm_LiuHelsenDesigns_OneD_lemma_15
-- name    : LiuHelsenDesigns.OneD.lemma_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T11:09:26.774074+00:00
-- url     : https://prove2.me/theorems/0c563a0a-32f4-40ed-ad63-2ee5c6950600
-- title:
--   Lemma 15 — overlapping permutation registers
-- statement:
--   There is an absolute positive constant C, uniform over all finite sets A, B, C and all orders k, such that the AB and BC permutation averages and the global ABC average satisfy
--
--   $$
--   \|E_{AB}^{(k)}E_{BC}^{(k)}-E_{ABC}^{(k)}\|_{2\to2}\le C\frac{(k\log_2k+\log_2|B|)^3}{\sqrt{|B|}}.
--   $$
--
--   The same bound holds for alternating-group averages if $k+2\le|A||B|$ and $k+2\le|B||C|$. When B is empty the error and the bound are both zero. Both group versions and all finite carriers are retained.
--
--   Differences from the source:
--   - encoding: the logarithmic ratio when the finite overlap B is empty → the right-hand side is explicitly zero at |B|=0; reason: the AB and BC averages then multiply to the global average (a zero-dimensional ambient space for positive order, 1×1 identities at order 0), so the error is zero there; the nonempty formula is unchanged
--   - encoding: unqualified logarithms inside O(·) resource or overlap bounds → binary logarithms inside bounds with uniform existential leading constants; reason: changing a fixed logarithm base multiplies these terms by a fixed positive factor, absorbed uniformly into the leading constants; explicit log₂ expressions are unchanged
-- source:
--   Guoding Liu, Jonas Helsen, STOC 2027 submission #221 (October 2026), p. 35, Lemma 15. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/221.pdf

import Definitions.Def_LiuHelsenDesigns_OneD_permutations

namespace LiuHelsenDesigns.OneD
theorem lemma_15 : ∃ C₀ : ℝ, 0 < C₀ ∧
    ∀ (A B C : Type) [Fintype A] [Fintype B] [Fintype C], ∀ k : ℕ,
      overlapError A B C k false ≤ C₀ * overlapBound (Fintype.card B) k ∧
      (k+2 ≤ Fintype.card A * Fintype.card B →
        k+2 ≤ Fintype.card B * Fintype.card C →
        overlapError A B C k true ≤ C₀ * overlapBound (Fintype.card B) k) := by sorry
end LiuHelsenDesigns.OneD
