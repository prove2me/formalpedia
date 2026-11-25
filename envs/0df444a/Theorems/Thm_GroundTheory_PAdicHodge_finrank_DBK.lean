-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_finrank_DBK
-- name    : GroundTheory.PAdicHodge.finrank_DBK
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:27:05.662395+00:00
-- url     : https://prove2.me/theorems/bf4afa86-506e-4650-863e-8a7ff278ad3b
-- title:
--   PAdic Hodge: finrank DBK
-- statement:
--   The PAdic Hodge construction uses the finrank DBK property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AdmissibleField.lean#L107-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AdmissibleField.lean#L107-L110

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

theorem GroundTheory.PAdicHodge.finrank_DBK [Nontrivial B]
    (hK : ∀ b : B, (∀ g : G, g • b = b) → ∃ k : K, algebraMap K B k = b) :
    finrank K (DBK G F K B ρ) = finrank (invariantRing G F B) (DB B ρ) := by sorry
