-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_finite_image_singularSet
-- name    : GroundTheory.Global.Elliptic.finite_image_singularSet
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:07.285833+00:00
-- url     : https://prove2.me/theorems/b14ffc44-d514-4ca4-8f5c-14cd1f5a7490
-- title:
--   Elliptic: finite image singular Set
-- statement:
--   The Elliptic construction uses the finite image singular Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticFunctions.lean#L123-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticFunctions.lean#L123-L133

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable (L : PeriodPair)
variable {L}
variable (L)
variable {L}
variable (L)

theorem GroundTheory.Global.Elliptic.finite_image_singularSet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : ℂ → E} (hf : Meromorphic f) (hp : IsPeriodic L f) :
    (Torus.mk L '' singularSet f).Finite := by sorry
