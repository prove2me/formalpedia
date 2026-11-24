-- Prove2me | Theorems.Thm_GlobalTheory_HeckeLocInt_inv_mul_int_of_left_congr
-- name    : GlobalTheory.HeckeLocInt.inv_mul_int_of_left_congr
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:06:26.316067+00:00
-- url     : https://prove2.me/theorems/3f038ac2-ff08-4525-92db-909a42c2da6c
-- title:
--   Hecke Loc Int: inv mul int of left congr
-- statement:
--   The Hecke Loc Int construction uses the inv mul int of left congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/HeckeDoubleCosetAdicCompletionInvMulIntegral.lean#L36-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/HeckeDoubleCosetAdicCompletionInvMulIntegral.lean#L36-L105

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

theorem GlobalTheory.HeckeLocInt.inv_mul_int_of_left_congr {n : ℕ} (ϖ : K) (k : ℕ)
    (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (a a' b b' g g' : GL (Fin n) K)
    (ha' : ∀ i j, Valued.v ((a' : Matrix (Fin n) (Fin n) K) i j) ≤ 1)
    (hai : ∀ i j, Valued.v (((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j) ≤ 1)
    (hbi : ∀ i j, Valued.v (((b⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j) ≤ 1)
    (hb' : ∀ i j, Valued.v ((b' : Matrix (Fin n) (Fin n) K) i j) ≤ 1)
    (hsub : ∀ i j, Valued.v ((a : Matrix (Fin n) (Fin n) K) i j -
      (a' : Matrix (Fin n) (Fin n) K) i j) < 1)
    (hg : (g : Matrix (Fin n) (Fin n) K) =
      (a : Matrix (Fin n) (Fin n) K) * Formalism.UG.diagJ n ϖ k * (b : Matrix (Fin n) (Fin n) K))
    (hg' : (g' : Matrix (Fin n) (Fin n) K) =
      (a' : Matrix (Fin n) (Fin n) K) * Formalism.UG.diagJ n ϖ k * (b' : Matrix (Fin n) (Fin n) K)) :
    ∀ i j, Valued.v (((g⁻¹ * g' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j) ≤ 1 := by sorry
