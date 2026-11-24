-- Prove2me | Theorems.Thm_GlobalTheory_HeckeLocInt_int_mul
-- name    : GlobalTheory.HeckeLocInt.int_mul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T14:03:29.827714+00:00
-- url     : https://prove2.me/theorems/b7562467-ebba-4d39-bed0-87087818a36f
-- title:
--   Hecke Loc Int: int mul
-- statement:
--   The Hecke Loc Int construction uses the int mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/HeckeDoubleCosetAdicCompletionInvMulIntegral.lean#L18-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/HeckeDoubleCosetAdicCompletionInvMulIntegral.lean#L18-L25

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_HeckeDoubleCosetAdicCompletionInvMulIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.HeckeLocInt
open Matrix
variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]

theorem GlobalTheory.HeckeLocInt.int_mul {n : ℕ} {M N : Matrix (Fin n) (Fin n) K}
    (hM : ∀ i j, Valued.v (M i j) ≤ 1) (hN : ∀ i j, Valued.v (N i j) ≤ 1) :
    ∀ i j, Valued.v ((M * N) i j) ≤ 1 := by sorry
