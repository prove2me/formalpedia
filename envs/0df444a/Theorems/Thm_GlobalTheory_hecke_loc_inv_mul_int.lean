-- Prove2me | Theorems.Thm_GlobalTheory_hecke_loc_inv_mul_int
-- name    : GlobalTheory.hecke_loc_inv_mul_int
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:55:06.825839+00:00
-- url     : https://prove2.me/theorems/af089c14-63a2-4cb2-b4e1-6b7df46ad55b
-- title:
--   Global Theory: hecke loc inv mul int
-- statement:
--   The Global Theory construction uses the hecke loc inv mul int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/HeckeDoubleCosetAdicCompletionInvMulIntegral.lean#L111-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/HeckeDoubleCosetAdicCompletionInvMulIntegral.lean#L111-L113

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
open GlobalTheory

theorem GlobalTheory.hecke_loc_inv_mul_int : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (ϖ : v.adicCompletion F) (k : ℕ), Valued.v ϖ = WithZero.exp (-1 : ℤ) → ∀ (a a' b b' g g' : GL (Fin n) (v.adicCompletion F)), (∀ i j, Valued.v ((a' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1) → (∀ i j, Valued.v (((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1) → (∀ i j, Valued.v (((b⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1) → (∀ i j, Valued.v ((b' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1) → (∀ i j, Valued.v ((a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j - (a' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) < 1) → (g : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = (a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Formalism.UG.diagJ n ϖ k * (b : Matrix (Fin n) (Fin n) (v.adicCompletion F)) → (g' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = (a' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Formalism.UG.diagJ n ϖ k * (b' : Matrix (Fin n) (Fin n) (v.adicCompletion F)) → ∀ i j, Valued.v (((g⁻¹ * g' : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ 1 := by sorry
