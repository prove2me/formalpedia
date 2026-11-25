-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_isAdmissible_iff_finrank_DBK
-- name    : GroundTheory.PAdicHodge.isAdmissible_iff_finrank_DBK
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:46:59.037974+00:00
-- url     : https://prove2.me/theorems/ff4f111d-f05e-4436-87f7-a2e7020ac87e
-- title:
--   PAdic Hodge: is Admissible iff finrank DBK
-- statement:
--   The PAdic Hodge construction uses the is Admissible iff finrank DBK property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AdmissibleField.lean#L129-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AdmissibleField.lean#L129-L133

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
variable [IsDomain B]

theorem GroundTheory.PAdicHodge.isAdmissible_iff_finrank_DBK
    (hK : ∀ b : B, (∀ g : G, g • b = b) → ∃ k : K, algebraMap K B k = b) :
    IsAdmissible B ρ ↔ finrank K (DBK G F K B ρ) = finrank F V := by sorry
