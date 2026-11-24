-- Prove2me | Theorems.Thm_GlobalTheory_Models_Cpt_Above_exists_lift
-- name    : GlobalTheory.Models.Cpt.Above.exists_lift
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:03:16.482818+00:00
-- url     : https://prove2.me/theorems/2dddb219-0008-49d8-837b-cdb5910ed092
-- title:
--   Above: exists lift
-- statement:
--   The Above construction uses the exists lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/OpenImmersionCompStructureEqGeneric.lean#L32-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/OpenImmersionCompStructureEqGeneric.lean#L32-L94

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GenericPartDenseProOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueLiftOfDensePart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_AuxiliaryInertOddPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_OpenImmersionCompStructureEqGeneric
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

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
open GlobalTheory.Models
open GlobalTheory GlobalTheory.Models

theorem GlobalTheory.Models.Cpt.Above.exists_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (U' : Scheme.{0}) (F' O' : Type) [Field F'] [CommRing O'] (c' : U' ⟶ Sp F') (t' : SAB H U') (β' : O' →+* F') (U'' : Scheme.{0}) (F'' O'' : Type) [Field F''] [CommRing O''] (c'' : U'' ⟶ Sp F'') (t'' : SAB H U'') (β'' : O'' →+* F'') (C : Cpt c t β) (C' : Cpt c' t' β') (C'' : Cpt c'' t'' β'') (b : O →+* O') (b' : O' →+* O'') (k' : F' →+* F'') (r : U' ⟶ U) (ν : SABMap t' t r) (a : C'.Above C b r ν) (r' : U'' ⟶ U') (ν' : SABMap t'' t' r') (f : C''.X ⟶ C.X) (mu : SABMap C''.t C.t f) (hf : f ≫ C.s = C''.s ≫ spMap (b'.comp b)), IsDedFrac β'' → β''.comp b' = k'.comp β' → r' ≫ c' = c'' ≫ spMap k' → C''.j ≫ f = r' ≫ r ≫ C.j → C''.m.φ ≫ mu.φ = ν'.φ ≫ ν.φ ≫ C.m.φ → ∃ (h : C''.X ⟶ C'.X) (mu' : SABMap C''.t C'.t h) (hh : h ≫ C'.s = C''.s ≫ spMap b'), h ≫ a.π = f ∧ mu'.φ ≫ a.mu.φ = mu.φ ∧ C''.j ≫ h = r' ≫ C'.j ∧ C''.m.φ ≫ mu'.φ = ν'.φ ≫ C'.m.φ ∧ (IsFinite (pullback.lift f C''.s hf) → IsFinite (pullback.lift h C''.s hh)) := by sorry
