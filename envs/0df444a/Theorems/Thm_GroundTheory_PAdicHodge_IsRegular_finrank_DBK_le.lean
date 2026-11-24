-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsRegular_finrank_DBK_le
-- name    : GroundTheory.PAdicHodge.IsRegular.finrank_DBK_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:46:41.306646+00:00
-- url     : https://prove2.me/theorems/bf731e86-9d7a-45cb-8486-d9978fa87e3a
-- title:
--   Is Regular: finrank DBK le
-- statement:
--   The Is Regular construction uses the finrank DBK le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AdmissibleField.lean#L123-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AdmissibleField.lean#L123-L127

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

theorem GroundTheory.PAdicHodge.IsRegular.finrank_DBK_le (h : IsRegular G F B)
    (hK : ∀ b : B, (∀ g : G, g • b = b) → ∃ k : K, algebraMap K B k = b) [FiniteDimensional F V] :
    finrank K (DBK G F K B ρ) ≤ finrank F V := by sorry
