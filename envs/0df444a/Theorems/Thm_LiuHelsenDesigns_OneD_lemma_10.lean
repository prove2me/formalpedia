-- Prove2me | Theorems.Thm_LiuHelsenDesigns_OneD_lemma_10
-- name    : LiuHelsenDesigns.OneD.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T11:09:59.204871+00:00
-- url     : https://prove2.me/theorems/9c8c377c-b0d6-4094-a26e-9b44bd036501
-- title:
--   Lemma 10 — alternating and symmetric ordinary moments
-- statement:
--   For an ℓ-qubit computational basis and every order $k\le2^\ell-2$, let P(π) be the actual permutation matrix. Then
--
--   $$
--   \mathbb E_{\pi\in\operatorname{Alt}(2^\ell)}P(\pi)^{\otimes k}=\mathbb E_{\pi\in\operatorname{Sym}(2^\ell)}P(\pi)^{\otimes k}.
--   $$
--
--   This is the ordinary permutation moment, not a balanced unitary moment.
--
--   Differences from the source: none.
-- source:
--   Guoding Liu, Jonas Helsen, STOC 2027 submission #221 (October 2026), p. 29, Lemma 10. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/221.pdf

import Definitions.Def_LiuHelsenDesigns_OneD_permutations

namespace LiuHelsenDesigns.OneD
theorem lemma_10 (ℓ k : ℕ) (hrange : k+2 ≤ 2^ℓ) :
    permutationAverage (Basis ℓ) k true = permutationAverage (Basis ℓ) k false := by sorry
end LiuHelsenDesigns.OneD
