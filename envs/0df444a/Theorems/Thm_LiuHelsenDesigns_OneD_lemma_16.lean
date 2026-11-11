-- Prove2me | Theorems.Thm_LiuHelsenDesigns_OneD_lemma_16
-- name    : LiuHelsenDesigns.OneD.lemma_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T11:09:56.659805+00:00
-- url     : https://prove2.me/theorems/7fd7ac14-fbbd-4b10-8100-316a66c5349a
-- title:
--   Lemma 16 — symplectic bounded products (corrected: exclude rank one)
-- statement:
--   There is an integer $1\le M\le200$, uniform in rank, such that for every $\ell\ge2$ one can choose M symplectic matrices gᵢ for which the canonical subgroup $G=\{\operatorname{diag}(h,(h^{-1})^T):h\in SL(\ell;\mathbb F_2)\}$ obeys
--
--   $$
--   Sp(2\ell;\mathbb F_2)=\prod_{i=1}^M g_iGg_i^{-1}.
--   $$
--
--   This is a fixed ordered product of conjugate subgroups, not merely generation by their union. Rank one is false for this embedding.
--
--   Differences from the source:
--   - correction: all ranks ℓ → ranks ℓ≥2; reason: at ℓ=1 the canonical SL(1,F₂) image is trivial and so are all conjugates, while Sp(2,F₂) has six elements
-- source:
--   Guoding Liu, Jonas Helsen, STOC 2027 submission #221 (October 2026), p. 36, Lemma 16. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/221.pdf

import Definitions.Def_LiuHelsenDesigns_OneD_groups

namespace LiuHelsenDesigns.OneD
/-- Corrected at rank one; the SL subgroup is the source's Eq. (236) image. -/
theorem lemma_16 : ∃ M : ℕ, 1 ≤ M ∧ M ≤ 200 ∧ ∀ ℓ : ℕ, 2 ≤ ℓ →
    ∃ gs : Fin M → Sp ℓ, ∀ g : Sp ℓ, ∃ hs : Fin M → SL ℓ,
      g.val = (List.ofFn (fun i => (gs i).val * leviMatrix (hs i).val * (gs i).val⁻¹)).prod := by sorry
end LiuHelsenDesigns.OneD
