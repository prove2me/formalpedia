-- Prove2me | Theorems.Thm_GlobalTheory_T_pairFst_preimage_restriction_bijective_closedImmersion
-- name    : GlobalTheory.T.pairFst_preimage_restriction_bijective_closedImmersion
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T15:56:03.535172+00:00
-- url     : https://prove2.me/theorems/fee6712e-76a2-59c5-90dd-df1ead3425f4
-- title:
--   T: pair Fst preimage restriction bijective closed Immersion
-- statement:
--   The T construction uses the pair Fst preimage restriction bijective closed Immersion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PairFstPreimageRestrictionBijectiveClosedImmersiStatement.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PairFstPreimageRestrictionBijectiveClosedImmersiStatement.lean#L12-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PairFstPreimageRestrictionBijectiveClosedImmersi
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PreUMono
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PairFstPreimageRestrictionBijectiveClosedImmersiStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.pairFst_preimage_restriction_bijective_closedImmersion : ∀ (R' : Type) [CommRing R'] (X Y Y' : Scheme.{0}) (ψ : Y ⟶ X) (χ : Y' ⟶ Y) [IsClosedImmersion χ] (q' : Y' ⟶ Sp R'), Function.Bijective (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).pull1 ∧ Function.Bijective (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).pull2 ∧ (CohomZeroIsConstants (OAff q') → CohomZeroIsConstants (pairFst ψ ⋙ OPre χ q')) := by sorry
