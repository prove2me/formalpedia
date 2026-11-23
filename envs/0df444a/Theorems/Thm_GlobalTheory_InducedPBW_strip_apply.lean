-- Prove2me | Theorems.Thm_GlobalTheory_InducedPBW_strip_apply
-- name    : GlobalTheory.InducedPBW.strip_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:47:09.199988+00:00
-- url     : https://prove2.me/theorems/0b548db9-58cc-44c3-a21b-62e549ed02ea
-- title:
--   Induced PBW: strip apply
-- statement:
--   The Induced PBW construction uses the strip apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DegreeSingleAdd.lean#L116-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DegreeSingleAdd.lean#L116-L117

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DegreeSingleAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.InducedPBW
variable {R : Type*} [CommRing R] {ι : Type*} {V : Type*} [AddCommGroup V] [Module R V]
variable {g : Type*} [LieRing g] [LieAlgebra R g]
variable [Fintype ι] [LinearOrder ι] (e : ι → g) (c : ι → g →ₗ[R] R) (act : g →ₗ[R] Module.End R V)
omit [Fintype ι] [LinearOrder ι]

theorem GlobalTheory.InducedPBW.strip_apply (s : Finset ι) (x : g) : strip e c s x = x - ∑ j ∈ s, c j x • e j := by sorry
