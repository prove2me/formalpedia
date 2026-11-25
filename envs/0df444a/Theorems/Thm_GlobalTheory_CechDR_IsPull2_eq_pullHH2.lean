-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_IsPull2_eq_pullHH2
-- name    : GlobalTheory.CechDR.IsPull2.eq_pullHH2
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:17:35.103794+00:00
-- url     : https://prove2.me/theorems/4b5acc97-1f99-4315-b7e2-c6d9d010182a
-- title:
--   Is Pull2: eq pull HH2
-- statement:
--   The Is Pull2 construction uses the eq pull HH2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PairResBijectiveTwo.lean#L126-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PairResBijectiveTwo.lean#L126-L127

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitMpOmjExtIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CommaDescentInjectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CommaDescentRestrictionEquivStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TwoCocycleCoboundaryOfBasisFunctorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneFormsTwoCocycleCoboundaryOfRestrictStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOneFormsCocycleRestrictSubCoboundaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HigherFormsOneCocycleCoboundaryOfRestrictStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CompatibleHigherFormsExtendAlongFunctorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasLocalisationAtElementsTrivSqZeroExtFormsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CommaFirstOrderCocycleLiftStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CommaSecondOrderCocycleLiftStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PairResBijectiveTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.CechDR
open FormExt FormExtJ
attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler
variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}
variable {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {σ : R →+* R'} {φ : X' ⟶ X} (h : φ ≫ s = s' ≫ spMap σ)

theorem GlobalTheory.CechDR.IsPull2.eq_pullHH2 {c : HH2 s} {c' : HH2 s'} (e : IsPull2 h c c') : c' = pullHH2 h c := by sorry
