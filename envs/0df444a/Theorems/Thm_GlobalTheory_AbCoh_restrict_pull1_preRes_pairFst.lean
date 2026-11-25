-- Prove2me | Theorems.Thm_GlobalTheory_AbCoh_restrict_pull1_preRes_pairFst
-- name    : GlobalTheory.AbCoh.restrict_pull1_preRes_pairFst
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T15:53:09.601316+00:00
-- url     : https://prove2.me/theorems/457b4838-7484-4151-83f9-dc601a791d65
-- title:
--   Ab Coh: restrict pull1 pre Res pair Fst
-- statement:
--   The Ab Coh construction uses the restrict pull1 pre Res pair Fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ObstructionClassNatural.lean#L24-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ObstructionClassNatural.lean#L24-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PreUMono
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PairFstPreimageRestrictionBijectiveClosedImmersi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CohomologyClassPullbackReductionPairs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CocyclePullbackIffPreimageAffineHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SurjectiveDeformationAffineSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ObstructionClassNatural
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory GlobalTheory.AbCoh

theorem GlobalTheory.AbCoh.restrict_pull1_preRes_pairFst {R' : Type} [CommRing R'] {X Y Y' : Scheme.{0}} (ψ : Y ⟶ X)
    (χ : Y' ⟶ Y) [IsAffineHom χ] (q' : Y' ⟶ Sp R') (y : HO1 q') :
    (CoefMap.restrict (OPre χ q') (pairFst ψ)).pull1 ((preRes χ q').pull1 y) =
      (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).pull1 y := by sorry
