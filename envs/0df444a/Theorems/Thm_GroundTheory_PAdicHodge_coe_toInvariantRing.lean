-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_coe_toInvariantRing
-- name    : GroundTheory.PAdicHodge.coe_toInvariantRing
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:26:30.485844+00:00
-- url     : https://prove2.me/theorems/b9be6f15-23fe-4d12-a485-fadc46d4958b
-- title:
--   PAdic Hodge: coe to Invariant Ring
-- statement:
--   The PAdic Hodge construction uses the coe to Invariant Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AdmissibleField.lean#L69-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AdmissibleField.lean#L69-L69

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_Admissible
import Definitions.Def_GroundTheory_PAdicHodge_AdmissibleField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open TensorProduct Module
variable (G F K B : Type*) [Group G] [Field F] [Field K] [CommRing B] [Algebra F K] [Algebra K B]
  [Algebra F B] [IsScalarTower F K B] [MulSemiringAction G B] [SMulCommClass G F B]
  [SMulCommClass G K B]
variable {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V)
variable {G F K B}
omit [Algebra F K] [IsScalarTower F K B]

theorem GroundTheory.PAdicHodge.coe_toInvariantRing (k : K) : (toInvariantRing G F K B k : B) = algebraMap K B k := by sorry

attribute [defeq] GroundTheory.PAdicHodge.coe_toInvariantRing
