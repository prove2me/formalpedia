-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_ColStep_Conj_wh_colGeR_conj
-- name    : GlobalTheory.CompanionTheory.TyFin.ColStep.Conj.wh_colGeR_conj
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:17:22.916259+00:00
-- url     : https://prove2.me/theorems/1e6f94b9-2dfe-4d77-a88f-0ac5823f0394
-- title:
--   Conj: wh col Ge R conj
-- statement:
--   The Conj construction uses the wh col Ge R conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WhittakerBlockEmbeddingConj.lean#L195-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WhittakerBlockEmbeddingConj.lean#L195-L215

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WhittakerBlockEmbeddingConj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.ColStep GlobalTheory.CompanionTheory.TyFin.ColStep.Conj
variable {K : Type} [Field K]

theorem GlobalTheory.CompanionTheory.TyFin.ColStep.Conj.wh_colGeR_conj : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ) (ψ₀ : AddChar K ℂ) (χ : GL (Fin d) K → ℂ) (g : GL (Fin j) K) (h : GL (Fin d) K) (r : Fin j → K),
    j < d → (∀ x y, χ (x * y * x⁻¹) = χ y) →
    (h : Matrix (Fin d) (Fin d) K) = blkEmb K d j (g : Matrix (Fin j) (Fin j) K) →
    ((h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = blkEmb K d j ((g⁻¹ : GL (Fin j) K) : Matrix (Fin j) (Fin j) K) →
    wh (colGe d j) (colGeR K d j r) ψ₀ χ = wh (colGe d j) (colGeR K d j (Matrix.vecMul r (g : Matrix (Fin j) (Fin j) K))) ψ₀ χ := by sorry
