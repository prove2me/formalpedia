-- Prove2me | Theorems.Thm_LabelSymmetricCollision215_Collision_lemma_3_5
-- name    : LabelSymmetricCollision215.Collision.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:57:44.722202+00:00
-- url     : https://prove2.me/theorems/0cd70caa-d61d-4f38-9f73-a9d7181279e5
-- title:
--   Lemma 3.5 — One-query collision progress
-- statement:
--   Let $\phi$ be any, possibly unnormalized, joint vector with no recorded collision, so $\Pi_{=0}\phi=\phi$. With $\Lambda_{\eta,I}$ the exact algorithm-basis and occupied-set sector projector,
--   $$\|\Pi_{\ge1}\widetilde O\phi\|\le\frac4{\sqrt N}\left(\sum_\eta\sum_{I\subseteq[M]}|I|\|\Lambda_{\eta,I}\phi\|^2\right)^{1/2}.$$
--   This bounds one-query collision progress for arbitrary collision-free vectors.
--
--   Differences from the source:
--   - encoding: zero start, WXY order and negative-exponent Fourier basis → published fixed unit start, XYW coordinates, with the value register explicitly changed to the same Fourier basis; reason: absorb fixed state preparation into U₀ and permute basis factors; neither operation changes queries, dimensions, or measured success
-- source:
--   Frédéric Magniez, Sebastian Zur, Tight Time-Space Lower Bounds for Collision Finding and Element Distinctness under Label Symmetry, STOC 2027 submission #215 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/215.pdf, Lemma 3.5, PDF 19 / printed 17

import Definitions.Def_LabelSymmetricCollision215_Collision_Tensor

namespace LabelSymmetricCollision215.Collision

/-- Magniez–Zur, Lemma 3.5, PDF 19 / printed 17. -/
theorem lemma_3_5 {M N : ℕ} {W : Type} [Fintype W] [NeZero N] (hM : 0 < M)
    (φ : H (Reg M N W × DB M N)) (hφ : freeProjection M N W φ = φ) :
    ‖collisionProjection M N W (recordingOracle M N W φ)‖ ≤
      4 / Real.sqrt N * Real.sqrt
        (∑ η : Reg M N W, ∑ I : Finset (Fin M),
          (I.card : ℝ) * ‖sectorProjection η I φ‖^2) := by sorry

end LabelSymmetricCollision215.Collision
