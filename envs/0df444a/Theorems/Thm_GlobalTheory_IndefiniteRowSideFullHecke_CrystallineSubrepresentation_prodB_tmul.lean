-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CrystallineSubrepresentation_prodB_tmul
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.prodB_tmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:10.314806+00:00
-- url     : https://prove2.me/theorems/bbcde890-35ce-4380-99b8-c13c07d218c8
-- title:
--   Crystalline Subrepresentation: prod B tmul
-- statement:
--   The Crystalline Subrepresentation construction uses the prod B tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/CrystallineSubrepresentation.lean#L99-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/CrystallineSubrepresentation.lean#L99-L101

import Mathlib
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineSubrepresentation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.prodB_tmul (v : V) (b : B) (v' : V') (b' : B) :
    prodB (LL := LL) ((v ⊗ₜ[Qp] b) ⊗ₜ[LL] (v' ⊗ₜ[Qp] b')) = (v ⊗ₜ[LL] v') ⊗ₜ[Qp] (b * b') := by sorry
