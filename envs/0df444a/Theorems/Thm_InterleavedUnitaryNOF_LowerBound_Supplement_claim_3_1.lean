-- Prove2me | Theorems.Thm_InterleavedUnitaryNOF_LowerBound_Supplement_claim_3_1
-- name    : InterleavedUnitaryNOF.LowerBound.Supplement.claim_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:46:36.827446+00:00
-- url     : https://prove2.me/theorems/642171f1-89ff-433f-a5f2-43eaed1ea11f
-- title:
--   Claim 3.1 — polar unitarity and ten-factor trace perturbation
-- statement:
--   Let $m\ge1$ be any integer, let $\sigma=10^{-4}$, and let all ten complex $m\times m$ input matrices satisfy $\|U^\dagger U-I_m\|_F\le\sigma$. Let $W=A_1B_1C_1D_1E_1A_2B_2C_2D_2E_2$ and form $\widetilde W$ by replacing each factor with $\widetilde U=U(\sqrt{U^\dagger U})^{-1}$ in exactly the same order. Then, for every input factor,
--
--   $$\widetilde U^\dagger\widetilde U=I_m,\qquad\|\widetilde U-U\|_{\rm op}\le\sigma,$$
--
--   and the full product satisfies
--
--   $$\frac{|\operatorname{Re}\operatorname{Tr}\widetilde W-\operatorname{Re}\operatorname{Tr}W|}{m}\le10\sigma(1+\sigma)^{9/2}.$$
--
--   This is the polar replacement and trace perturbation claim supporting the quantum companion theorem. It includes non-power-of-two dimensions and all complex near-unitary inputs, with no invertibility assumption.
--
--   Differences from the source:
--   - encoding: positive-dimensional matrices and the ten factors grouped as X, Y, Z → Fin m indices and membership in the union of the three published MatrixInput ranges; reason: zero-based indices and tuple grouping preserve every factor and every positive dimension
--   - encoding: the positive inverse square root in the unitary polar replacement → CFC.sqrt of the Gram matrix followed by total matrix inversion; reason: the original Frobenius promise makes the Gram matrix positive definite, so the total conventions change no promised instance
--   - encoding: Euclidean-induced operator norm and exponent 9/2 → CStarMatrix norm and Real.rpow at exponent (9 : ℝ)/2; reason: these denote the same real norm and exponent, without natural-number truncation
-- source:
--   Haoyu Wang, Pei Wu, Guangxu Yang, STOC 2027 submission #1513 (October 2026), Claim 3.1, p.8; proof pp.22

import Mathlib
import Definitions.Def_InterleavedUnitaryNOF_LowerBound_Supplement_Polar

namespace InterleavedUnitaryNOF.LowerBound.Supplement

/-- Claim 3.1, p.8, with σ=10⁻⁴ fixed immediately before the claim.
The support statement applies to every positive integer dimension, independently
of the power-of-two convention for encoded quantum inputs. -/
theorem claim_3_1 (m : ℕ) (hm : 0 < m) (u : MatrixInput m)
    (hu : promisedMatrices u) :
    (∀ U : Mat m, (U ∈ Set.range u.1 ∨ U ∈ Set.range u.2.1 ∨ U ∈ Set.range u.2.2) →
      (polar U).conjTranspose * polar U = 1 ∧
      opNorm (polar U - U) ≤ (1 : ℝ)/10000) ∧
    |(Matrix.trace (word (polarInput u))).re - (Matrix.trace (word u)).re| / m ≤
      10 * ((1 : ℝ)/10000) * Real.rpow (1 + (1 : ℝ)/10000) ((9 : ℝ)/2) := by sorry

end InterleavedUnitaryNOF.LowerBound.Supplement
