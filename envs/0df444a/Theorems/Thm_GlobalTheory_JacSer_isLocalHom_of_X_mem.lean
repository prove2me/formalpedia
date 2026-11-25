-- Prove2me | Theorems.Thm_GlobalTheory_JacSer_isLocalHom_of_X_mem
-- name    : GlobalTheory.JacSer.isLocalHom_of_X_mem
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:07:29.508406+00:00
-- url     : https://prove2.me/theorems/f62862f6-9e80-490a-bef0-fdde2e0b548e
-- title:
--   Jac Ser: is Local Hom of X mem
-- statement:
--   The Jac Ser construction uses the is Local Hom of X mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/JacEqUnitMulDetPderiv.lean#L72-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/JacEqUnitMulDetPderiv.lean#L72-L77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsLieBasisIffIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MemNonzeroLocusVia
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_JacEqUnitMulDetPderiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.JacSer
open IsLocalRing MvPowerSeries GlobalTheory.SqZero
variable {O : Type} [CommRing O] [IsLocalRing O]
variable [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]
omit [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]

theorem GlobalTheory.JacSer.isLocalHom_of_X_mem {n : ℕ} (e : MvPowerSeries (Fin n) O →ₐ[O] O) (he : ∀ i, e (X i) ∈ maximalIdeal O) :
    IsLocalHom e.toRingHom := by sorry
