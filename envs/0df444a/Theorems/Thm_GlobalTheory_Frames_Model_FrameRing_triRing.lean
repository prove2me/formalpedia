-- Prove2me | Theorems.Thm_GlobalTheory_Frames_Model_FrameRing_triRing
-- name    : GlobalTheory.Frames.Model.FrameRing.triRing
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:06:37.021405+00:00
-- url     : https://prove2.me/theorems/b542eb8c-23f4-5143-b0fd-6f5a23d50450
-- title:
--   Frame Ring: tri Ring
-- statement:
--   The Frame Ring construction uses the tri Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ExistenceOfLattices/FrameRingGlRing.lean#L156-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ExistenceOfLattices/FrameRingGlRing.lean#L156-L196

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

theorem GlobalTheory.Frames.Model.FrameRing.triRing {A : Type} [CommRing A] [Algebra K A] {π : R →ₐ[K] A}
    {X : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) A} {s : Aˣ} (h : FrameRing m π X s) :
    let I : Ideal A := Ideal.span {x | ∃ τ i j, i < j ∧ x = X τ i j}
    TriRing m ((Ideal.Quotient.mkₐ K I).comp π) (fun τ => (X τ).map (Ideal.Quotient.mk I))
      (Units.map (Ideal.Quotient.mk I).toMonoidHom s) := by sorry
