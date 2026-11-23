-- Prove2me | Theorems.Thm_GlobalTheory_hasEnoughRootsOfUnity_globalSections
-- name    : GlobalTheory.hasEnoughRootsOfUnity_globalSections
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:20.532337+00:00
-- url     : https://prove2.me/theorems/6cf2629e-fc6a-4fd7-93aa-005696212812
-- title:
--   Global Theory: has Enough Roots Of Unity global Sections
-- statement:
--   The Global Theory construction uses the has Enough Roots Of Unity global Sections property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/HasEnoughRootsOfUnityGlobalSections.lean#L79-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/HasEnoughRootsOfUnityGlobalSections.lean#L79-L86

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_HasEnoughRootsOfUnityGlobalSections
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem GlobalTheory.hasEnoughRootsOfUnity_globalSections (K : Type) [Field K] [IsAlgClosed K] (N : ℕ)
    (hN : (N : K) ≠ 0) :
    HasEnoughRootsOfUnity Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) N := by sorry
