-- Prove2me | Theorems.Thm_LabelSymmetricCollision215_Collision_lemma_3_3
-- name    : LabelSymmetricCollision215.Collision.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:57:47.06355+00:00
-- url     : https://prove2.me/theorems/99802d4b-b4c0-4b0f-a794-709a0f4d3340
-- title:
--   Lemma 3.3 — Recording-query coefficients
-- statement:
--   Let $p$ be a nonzero cyclic label and write $\omega_N=e^{2\pi i/N}$. A recording query at address $x$ fixes the algorithm basis value and every database cell other than $x$. At $x$ its matrix coefficients are
--   $$\gamma_{y,\bot}=\frac{\omega_N^{py}}{\sqrt N},\quad\gamma_{\bot,\bot}=0,\quad\gamma_{\bot,z}=\frac{\omega_N^{pz}}{\sqrt N},$$
--   $$\gamma_{y,z}=\frac{1-\omega_N^{py}-\omega_N^{pz}}N\ (y\ne z),\qquad\gamma_{y,y}=\frac{1+(N-2)\omega_N^{py}}N.$$
--   For $p=0$ every register is unchanged. The statement includes the full basis-vector transformation, which sums over the replacement value of the queried cell. These coefficients describe arbitrary cyclic ranges.
--
--   Differences from the source:
--   - encoding: zero start, WXY order and negative-exponent Fourier basis → published fixed unit start, XYW coordinates, with the value register explicitly changed to the same Fourier basis; reason: absorb fixed state preparation into U₀ and permute basis factors; neither operation changes queries, dimensions, or measured success
-- source:
--   Frédéric Magniez, Sebastian Zur, Tight Time-Space Lower Bounds for Collision Finding and Element Distinctness under Label Symmetry, STOC 2027 submission #215 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/215.pdf, Lemma 3.3, PDF 17 / printed 15

import Definitions.Def_LabelSymmetricCollision215_Collision_Tensor

namespace LabelSymmetricCollision215.Collision

/-- Magniez–Zur, Lemma 3.3, PDF 17 / printed 15. -/
theorem lemma_3_3 {M N : ℕ} {W : Type} [Fintype W] [NeZero N] (hM : 0 < M) :
    (∀ (p : ZMod N), p ≠ 0 →
      (∀ y, recordingCell N p (some y) none = phase p y / (Real.sqrt N : ℂ)) ∧
      recordingCell N p none none = 0 ∧
      (∀ z, recordingCell N p none (some z) = phase p z / (Real.sqrt N : ℂ)) ∧
      (∀ y z, y ≠ z → recordingCell N p (some y) (some z) =
        (1 - phase p y - phase p z) / (N : ℂ)) ∧
      (∀ y, recordingCell N p (some y) (some y) =
        (1 + phase p y * ((N : ℂ)-2)) / (N : ℂ))) ∧
    (∀ (η : Reg M N W) (d : DB M N),
      recordingOracle M N W (basis (η,d)) =
        ∑ y : Option (ZMod N), recordingCell N η.1.2 y (d η.1.1) •
          basis (η, Function.update d η.1.1 y)) ∧
    (∀ (η : Reg M N W) (d : DB M N), η.1.2 = 0 →
      recordingOracle M N W (basis (η,d)) = basis (η,d)) := by sorry

end LabelSymmetricCollision215.Collision
