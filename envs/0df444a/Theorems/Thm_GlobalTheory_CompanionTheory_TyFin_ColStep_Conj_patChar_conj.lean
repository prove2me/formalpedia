-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_ColStep_Conj_patChar_conj
-- name    : GlobalTheory.CompanionTheory.TyFin.ColStep.Conj.patChar_conj
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:17:21.909053+00:00
-- url     : https://prove2.me/theorems/3e1f6e08-9357-40df-9703-e75c83bf7f44
-- title:
--   Conj: pat Char conj
-- statement:
--   The Conj construction uses the pat Char conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WhittakerBlockEmbeddingConj.lean#L164-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WhittakerBlockEmbeddingConj.lean#L164-L193

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

theorem GlobalTheory.CompanionTheory.TyFin.ColStep.Conj.patChar_conj {d j : ℕ} (hj : j < d) (ψ₀ : AddChar K ℂ) (g : GL (Fin j) K)
    (h : GL (Fin d) K) (r : Fin j → K)
    (h1 : (h : Matrix (Fin d) (Fin d) K) = blkEmb K d j (g : Matrix (Fin j) (Fin j) K))
    (h2 : ((h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      blkEmb K d j ((g⁻¹ : GL (Fin j) K) : Matrix (Fin j) (Fin j) K))
    (u : GL (Fin d) K) :
    patChar (colGeR K d j r) ψ₀ (h * u * h⁻¹) =
      patChar (colGeR K d j (Matrix.vecMul r (g : Matrix (Fin j) (Fin j) K))) ψ₀ u := by sorry
