-- Prove2me | Theorems.Thm_GlobalTheory_HilbFam_JetModular_jet_smul
-- name    : GlobalTheory.HilbFam.JetModular.jet_smul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:08:31.311331+00:00
-- url     : https://prove2.me/theorems/30938d7f-6b89-49da-976c-3a3fc0882e98
-- title:
--   Jet Modular: jet smul
-- statement:
--   The Jet Modular construction uses the jet smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HilbertEisensteinLatticeJetSl2IntSmul.lean#L102-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HilbertEisensteinLatticeJetSl2IntSmul.lean#L102-L118

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedPartialDerivConstMulReindexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinValueLinearChangeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinLatticeJetSl2IntSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HilbFam GlobalTheory.HilbFam.JetModular
open NumberField UpperHalfPlane
open scoped Classical MatrixGroups nonZeroDivisors
set_option autoImplicit false

theorem GlobalTheory.HilbFam.JetModular.jet_smul : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (L : _root_.GlobalTheory.HilbFam.Lat F) (κ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ) (γ : SL(2, ℤ)) (τ : ℍ) (c t : ℂ), Even k → _root_.GlobalTheory.HilbFam.jet k L κ ((γ • τ : ℍ) : ℂ) c t = (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) : ℂ) ^ (k * Module.finrank ℚ F) * _root_.GlobalTheory.HilbFam.jet k (_root_.GlobalTheory.HilbFam.mulMat L (γ : Matrix (Fin 2) (Fin 2) ℤ)) κ τ (c - t * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1)) (t * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) ^ 2) := by sorry
