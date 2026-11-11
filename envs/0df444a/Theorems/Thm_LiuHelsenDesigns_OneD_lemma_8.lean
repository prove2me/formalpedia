-- Prove2me | Theorems.Thm_LiuHelsenDesigns_OneD_lemma_8
-- name    : LiuHelsenDesigns.OneD.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T11:09:29.338653+00:00
-- url     : https://prove2.me/theorems/0218f368-95f7-43fc-8c5f-93282ae77f70
-- title:
--   Lemma 8 — collective suppression of non-permutation commutants
-- statement:
--   Let $5\le k\le\xi-1$, $\ell<\xi$ and $2^\ell\ge k^8$. For a stochastic Lagrangian T let $f_\ell(T)=\|\Phi_{H,\ell}^{(k)}(R_\ell(T))\|_{2\to2}$. Then
--
--   $$
--   \sum_{T\in\Sigma_{k,k}\setminus S_k}f_\ell(T)^{2\xi/\ell}\le k!2^k\left(\frac{k^4}{2^\ell}\right)^{2\xi/\ell}.
--   $$
--
--   The real exponent is not truncated integer division. The estimate aggregates the entire non-permutation sector.
--
--   Differences from the source: none.
-- source:
--   Guoding Liu, Jonas Helsen, STOC 2027 submission #221 (October 2026), p. 19, Lemma 8. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/221.pdf

import Definitions.Def_LiuHelsenDesigns_OneD_commutants

namespace LiuHelsenDesigns.OneD
attribute [local instance] Classical.propDecidable
theorem lemma_8 (ξ ℓ k : ℕ) (hk : 5 ≤ k) (hrange : k + 1 ≤ ξ)
    (hl : ℓ < ξ) (hd : (k : ℝ)^8 ≤ (2 : ℝ)^ℓ) :
    (∑ T : Sigma k, if ¬PermutationSector T then
      Real.rpow (suppression ℓ k T) (2 * (ξ : ℝ) / ℓ) else 0) ≤
      (k.factorial : ℝ) * (2 : ℝ)^k *
        Real.rpow ((k : ℝ)^4 / (2 : ℝ)^ℓ) (2 * (ξ : ℝ) / ℓ) := by sorry
end LiuHelsenDesigns.OneD
