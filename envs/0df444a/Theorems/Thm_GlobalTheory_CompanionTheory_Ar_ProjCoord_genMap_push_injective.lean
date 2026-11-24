-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_ProjCoord_genMap_push_injective
-- name    : GlobalTheory.CompanionTheory.Ar.ProjCoord.genMap_push_injective
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:18:57.822805+00:00
-- url     : https://prove2.me/theorems/b8b779bc-e729-4fb7-850f-c8af0d937c9c
-- title:
--   Proj Coord: gen Map push injective
-- statement:
--   The Proj Coord construction uses the gen Map push injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/ZarhinBundleKernelFirstCoordEquations.lean#L44-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/ZarhinBundleKernelFirstCoordEquations.lean#L44-L49

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_CoordsAt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InjectiveOfIsCptGen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_ZarhinBundleKernelFirstCoordEquations
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.ProjCoord
variable {X Y : Scheme.{0}} {Ω : Type} [Field Ω]

theorem GlobalTheory.CompanionTheory.Ar.ProjCoord.genMap_push_injective (η : Spec (CommRingCat.of Ω) ⟶ Y) (f : Y ⟶ X) [IsOpenImmersion f]
    (p : Cpt η) (h : Function.Injective (genMap η p)) :
    Function.Injective (genMap (η ≫ f) (push η f p)) := by sorry
