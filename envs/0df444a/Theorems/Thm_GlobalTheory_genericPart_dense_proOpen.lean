-- Prove2me | Theorems.Thm_GlobalTheory_genericPart_dense_proOpen
-- name    : GlobalTheory.genericPart_dense_proOpen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:36:42.544669+00:00
-- url     : https://prove2.me/theorems/80668f9a-969f-4113-88ac-8d6a63ffdb78
-- title:
--   Global Theory: generic Part dense pro Open
-- statement:
--   The Global Theory construction uses the generic Part dense pro Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/GenericPartDenseProOpen.lean#L30-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/GenericPartDenseProOpen.lean#L30-L67

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GenericPartDenseProOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj TensorProduct Pointwise

theorem GlobalTheory.genericPart_dense_proOpen : ∀ (O F : Type) [CommRing O] [IsDedekindDomain O] [Field F] [Algebra O F] [IsFractionRing O F] (X U : Scheme.{0}) (s : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O) (jQ : U ⟶ pullback s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap O F))), Flat s → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver s → IsOpenImmersion jQ → Dense (Set.range jQ) → IsLocallyNoetherian X ∧ CompactSpace X ∧ X.IsSeparated ∧ IsPreimmersion (jQ ≫ pullback.fst _ _) ∧ Flat (jQ ≫ pullback.fst _ _) ∧ IsDominant (jQ ≫ pullback.fst _ _) ∧ QuasiCompact (jQ ≫ pullback.fst _ _) := by sorry
