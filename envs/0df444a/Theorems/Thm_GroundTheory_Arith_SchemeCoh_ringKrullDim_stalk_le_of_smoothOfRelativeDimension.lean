-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ringKrullDim_stalk_le_of_smoothOfRelativeDimension
-- name    : GroundTheory.Arith.SchemeCoh.ringKrullDim_stalk_le_of_smoothOfRelativeDimension
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:53:22.088278+00:00
-- url     : https://prove2.me/theorems/406e32d2-8049-4626-8fc2-dc5acebe513f
-- title:
--   Scheme Coh: ring Krull Dim stalk le of smooth Of Relative Dimension
-- statement:
--   The Scheme Coh construction uses the ring Krull Dim stalk le of smooth Of Relative Dimension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularCurve.lean#L66-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularCurve.lean#L66-L94

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularSmooth
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularCurve
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open IsLocalRing
universe u
open AlgebraicGeometry CategoryTheory

theorem GroundTheory.Arith.SchemeCoh.ringKrullDim_stalk_le_of_smoothOfRelativeDimension {X : Scheme.{u}} {k : Type u} [Field k]
    (n : ℕ) (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f] (x : X) :
    ringKrullDim (X.presheaf.stalk x) ≤ n := by sorry
