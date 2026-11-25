-- Prove2me | Theorems.Thm_GlobalTheory_T_wedge_property_from_fibres
-- name    : GlobalTheory.T.wedge_property_from_fibres
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T15:46:17.404819+00:00
-- url     : https://prove2.me/theorems/d136c375-ebf6-49e5-91e8-d5abae9d6575
-- title:
--   T: wedge property from fibres
-- statement:
--   The T construction uses the wedge property from fibres property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WedgePropertyFromFibresStatement.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WedgePropertyFromFibresStatement.lean#L11-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WedgePropertyFromFibres
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WedgePropertyFromFibresStatement
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_cup

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

theorem GlobalTheory.T.wedge_property_from_fibres : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), Module.Finite R (HO1 s) → Module.Projective R (HO1 s) → Module.Finite R (HO2 s) → Module.Projective R (HO2 s) → StructureSheafH1BaseChange s → StructureSheafH2BaseChange s → (∀ x : HO1 s, cup _ x x = 0) → (∀ (k : Type) [Field k] [Algebra R k] (X' : Scheme.{0}) (s' : X' ⟶ Sp k) (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap (algebraMap R k))), WedgeO (OAff s')) → WedgeO (OAff s) := by sorry
