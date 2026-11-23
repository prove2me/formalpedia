-- Prove2me | Theorems.Thm_GlobalTheory_HermSign_realMap_tmul
-- name    : GlobalTheory.HermSign.realMap_tmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:03:20.000604+00:00
-- url     : https://prove2.me/theorems/48f20b75-7741-4710-bff4-4d87be1ccb51
-- title:
--   Herm Sign: real Map tmul
-- statement:
--   The Herm Sign construction uses the real Map tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/SignatureHermitianModelOfDatum.lean#L295-L297
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/SignatureHermitianModelOfDatum.lean#L295-L297

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {r : ℕ}
  (Φ : CMType E) (φ : D.La →ₗ[𝓞 E] (Fin r → E))

theorem GlobalTheory.HermSign.realMap_tmul (t : ℝ) (x : D.La) (τ : Φ) (i : Fin r) :
    realMap D Φ φ (t ⊗ₜ x) τ i = t * τ.1 (φ x i) := by sorry
