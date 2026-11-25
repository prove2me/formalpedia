-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_toInvariantRing_bijective
-- name    : GroundTheory.PAdicHodge.toInvariantRing_bijective
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:47:22.414199+00:00
-- url     : https://prove2.me/theorems/9905c9a0-a238-452f-beab-e789450102fc
-- title:
--   PAdic Hodge: to Invariant Ring bijective
-- statement:
--   The PAdic Hodge construction uses the to Invariant Ring bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AdmissibleField.lean#L72-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AdmissibleField.lean#L72-L78

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

theorem GroundTheory.PAdicHodge.toInvariantRing_bijective [Nontrivial B]
    (hK : ∀ b : B, (∀ g : G, g • b = b) → ∃ k : K, algebraMap K B k = b) :
    Function.Bijective (toInvariantRing G F K B) := by sorry
