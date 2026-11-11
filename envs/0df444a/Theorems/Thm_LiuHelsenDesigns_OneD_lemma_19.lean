-- Prove2me | Theorems.Thm_LiuHelsenDesigns_OneD_lemma_19
-- name    : LiuHelsenDesigns.OneD.lemma_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T11:07:40.573757+00:00
-- url     : https://prove2.me/theorems/ac3bc93b-6a1c-4f51-afee-5b3e75438afb
-- title:
--   Lemma 19 — three-factor special-linear decomposition
-- statement:
--   Let the binary vector space be A⊕B⊕C, with dimensions a,b,c and $b\ge2c$. Every special-linear transformation M of this space has the factorization
--
--   $$
--   M=(P_{AB}\oplus I_C)(I_A\oplus R_{BC})(Q_{AB}\oplus I_C).
--   $$
--
--   The factors act on the stated registers. Over the binary field every invertible linear transformation has determinant one, including zero-dimensional blocks.
--
--   Differences from the source:
--   - encoding: special-linear matrices over F₂ → invertible linear equivalences of the three product registers; reason: every invertible determinant over F₂ is one, and the product coordinates are the source direct sum
-- source:
--   Guoding Liu, Jonas Helsen, STOC 2027 submission #221 (October 2026), p. 38, Lemma 19. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/221.pdf

import Definitions.Def_LiuHelsenDesigns_OneD_elementary

namespace LiuHelsenDesigns.OneD
/-- Over F₂ every invertible linear transformation has determinant one. -/
theorem lemma_19 (a b c : ℕ) (hb : 2*c ≤ b)
    (M : (Register a × (Register b × Register c)) ≃ₗ[ZMod 2]
      (Register a × (Register b × Register c))) :
    ∃ P Q : (Register a × Register b) ≃ₗ[ZMod 2] (Register a × Register b),
    ∃ R : (Register b × Register c) ≃ₗ[ZMod 2] (Register b × Register c),
      ∀ v, M v = onAB P (onBC R (onAB Q v)) := by sorry
end LiuHelsenDesigns.OneD
