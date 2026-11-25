-- Prove2me | Theorems.Thm_GlobalTheory_HostModel_arcIn_be_even
-- name    : GlobalTheory.HostModel.arcIn_be_even
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T17:38:43.409581+00:00
-- url     : https://prove2.me/theorems/21d5114a-317e-4feb-b8a9-5e1c2c6cbe61
-- title:
--   Host Model: arc In be even
-- statement:
--   The Host Model construction uses the arc In be even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/IsPrimitiveRootArcRoot.lean#L302-L303
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/IsPrimitiveRootArcRoot.lean#L302-L303

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ToMatrixTrFormBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_TrFormBaseChangeNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_SqrtNegDiscMemCoeffField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ZeroFLeftExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_PullTopZFConstUnit
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsPrimitiveRootArcRoot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HostModel
open ToricData ConjDual
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {H : Host E} {l : Level H} (c : Coeff l) (k : Type) [CommRing k] [IsDomain k] (bF : c.F →+* k)

theorem GlobalTheory.HostModel.arcIn_be_even (y : 𝓞 E) : (2 : ℤ) ∣ (arcIn c k bF).be y y := by sorry
