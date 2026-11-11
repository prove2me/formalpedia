-- Prove2me | Theorems.Thm_LiuHelsenDesigns_OneD_lemma_9
-- name    : LiuHelsenDesigns.OneD.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T11:09:36.746208+00:00
-- url     : https://prove2.me/theorems/28329b1b-be0e-4b84-b319-79a4b1beffdc
-- title:
--   Lemma 9 — replacement by approximate magic blocks
-- statement:
--   Let ν be an ℓ-qubit relative-error k-design of error $\varepsilon\ge0$, of any order k. For every stochastic Lagrangian T,
--
--   $$
--   \|\Phi_\nu^{(k)}(R_\ell(T))\|_{2\to2}\le(1+\varepsilon2^{2\ell k})\|\Phi_{H,\ell}^{(k)}(R_\ell(T))\|_{2\to2}.
--   $$
--
--   This is the source’s multiplicative estimate for replacing exact local Haar blocks.
--
--   Differences from the source: none.
-- source:
--   Guoding Liu, Jonas Helsen, STOC 2027 submission #221 (October 2026), p. 19, Lemma 9. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/221.pdf

import Definitions.Def_LiuHelsenDesigns_OneD_commutants

namespace LiuHelsenDesigns.OneD
theorem lemma_9 (ℓ k : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (ν : MeasureTheory.Measure (Mat ℓ)) (hν : RelativeDesign ν k ε) (T : Sigma k) :
    matrixNorm (twirl ν k (commutantMatrix ℓ k T)) ≤
      (1 + ε * (2 : ℝ)^(2*ℓ*k)) * suppression ℓ k T := by sorry
end LiuHelsenDesigns.OneD
