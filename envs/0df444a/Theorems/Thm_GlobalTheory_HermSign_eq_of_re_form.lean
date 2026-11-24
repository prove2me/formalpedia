-- Prove2me | Theorems.Thm_GlobalTheory_HermSign_eq_of_re_form
-- name    : GlobalTheory.HermSign.eq_of_re_form
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:18:43.614276+00:00
-- url     : https://prove2.me/theorems/abc35b2a-eb2e-4646-a0f0-a7a24fe2d9dd
-- title:
--   Herm Sign: eq of re form
-- statement:
--   The Herm Sign construction uses the eq of re form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/SignatureHermitianModelOfDatum.lean#L100-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/SignatureHermitianModelOfDatum.lean#L100-L109

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_MemIffConjugateNotMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SignatureHermitianModelOfDatum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors TensorProduct ComplexConjugate ComplexOrder MatrixOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HermSign

theorem GlobalTheory.HermSign.eq_of_re_form {r : ℕ} (A B : Matrix (Fin r) (Fin r) ℂ) (z : ℂ) (hz : z ≠ 0)
    (h : ∀ u v : Fin r → ℂ, (z * (u ⬝ᵥ A *ᵥ star v)).re = (z * (u ⬝ᵥ B *ᵥ star v)).re) : A = B := by sorry
