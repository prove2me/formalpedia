-- Prove2me | Theorems.Thm_GlobalTheory_IdCompOpen_isOpen_sectionComponents_of_family
-- name    : GlobalTheory.IdCompOpen.isOpen_sectionComponents_of_family
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:52:02.345061+00:00
-- url     : https://prove2.me/theorems/aa933cc8-c5d3-40e7-9c42-09fb0a13e0ed
-- title:
--   Id Comp Open: is Open section Components of family
-- statement:
--   The Id Comp Open construction uses the is Open section Components of family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOpenIdentityComponentsSmoothGroupScheme.lean#L13-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOpenIdentityComponentsSmoothGroupScheme.lean#L13-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOpenNbhdSectionFibreIsPreirreducibleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenSndImageMulMemOpenGroupSchemeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemUnitComponentMulMemStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemIdentityComponentsOfMulInvStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenOfStableUnderGeneralizationOfLocallyClosedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StableUnderGeneralizationSectionComponentsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenIdentityComponentsSmoothGroupScheme
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IdCompOpen

theorem GlobalTheory.IdCompOpen.isOpen_sectionComponents_of_family (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X)
    (hf : Smooth f) (he : e ≫ f = 𝟙 _) (O : X.Opens → Set X) (hO : ∀ U, IsOpen (O U))
    (h1 : ∀ (U : X.Opens) (y : X), e (f y) ∈ U →
      y ∈ {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} → y ∈ O U)
    (h2 : ∀ (U : X.Opens) (y : X),
      (∀ z ∈ U, f z = f y → z ∈ {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))}) →
      y ∈ O U → y ∈ {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))}) :
    IsOpen {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} := by sorry
