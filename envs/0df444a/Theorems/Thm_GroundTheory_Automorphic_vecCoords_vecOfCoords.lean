-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_vecCoords_vecOfCoords
-- name    : GroundTheory.Automorphic.vecCoords_vecOfCoords
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:36:56.123821+00:00
-- url     : https://prove2.me/theorems/dd975a17-6bf4-4375-8096-fcc3bf736f0b
-- title:
--   Automorphic: vec Coords vec Of Coords
-- statement:
--   The Automorphic construction uses the vec Coords vec Of Coords property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DefiniteClassNumber/Places.lean#L94-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DefiniteClassNumber/Places.lean#L94-L97

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_HermTraceSelfOfHermValue
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_Places
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Module Matrix TensorProduct NumberField NumberField.InfinitePlace
variable {K : Type*} [Field K] [NumberField K]
variable {E : Type*} [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)
variable (R : Type*) [CommRing R] [Algebra K R]
omit [NumberField K] [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι]

theorem GroundTheory.Automorphic.vecCoords_vecOfCoords (c : ι × κ → R) : vecCoords R b (vecOfCoords b R c) = c := by sorry
