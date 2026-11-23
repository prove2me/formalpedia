-- Prove2me | Theorems.Thm_GlobalTheory_Frames_Model_FrameRing_injective
-- name    : GlobalTheory.Frames.Model.FrameRing.injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:51:39.021593+00:00
-- url     : https://prove2.me/theorems/1164e21d-1532-453c-be78-d999651c09a9
-- title:
--   Frame Ring: injective
-- statement:
--   The Frame Ring construction uses the injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ExistenceOfLattices/FrameRingGlRing.lean#L131-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ExistenceOfLattices/FrameRingGlRing.lean#L131-L138

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_FrameRingGlRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Frames GlobalTheory.Frames.Model
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {K : Type} [Field K] {J : Type} (m : J → ℕ) (R : Type) [CommRing R] [Algebra K R]
variable {m R}

theorem GlobalTheory.Frames.Model.FrameRing.injective {A : Type} [CommRing A] [Algebra K A] {π : R →ₐ[K] A}
    {X : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) A} {s : Aˣ} (h : FrameRing m π X s) : Function.Injective π := by sorry
