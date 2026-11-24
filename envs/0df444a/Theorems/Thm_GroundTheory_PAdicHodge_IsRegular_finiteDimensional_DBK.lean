-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsRegular_finiteDimensional_DBK
-- name    : GroundTheory.PAdicHodge.IsRegular.finiteDimensional_DBK
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:46:07.45216+00:00
-- url     : https://prove2.me/theorems/f0d76dee-dc73-4f4e-97e9-c245660cf2a7
-- title:
--   Is Regular: finite Dimensional DBK
-- statement:
--   The Is Regular construction uses the finite Dimensional DBK property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AdmissibleField.lean#L114-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AdmissibleField.lean#L114-L121

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

theorem GroundTheory.PAdicHodge.IsRegular.finiteDimensional_DBK (h : IsRegular G F B)
    (hK : ∀ b : B, (∀ g : G, g • b = b) → ∃ k : K, algebraMap K B k = b) [FiniteDimensional F V] :
    FiniteDimensional K (DBK G F K B ρ) := by sorry
