-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_ColStep_Conj_conj_mem
-- name    : GlobalTheory.CompanionTheory.TyFin.ColStep.Conj.conj_mem
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:17:14.276154+00:00
-- url     : https://prove2.me/theorems/e37a0ca6-f670-4f4c-80c3-d9c93e429da2
-- title:
--   Conj: conj mem
-- statement:
--   The Conj construction uses the conj mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WhittakerBlockEmbeddingConj.lean#L104-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WhittakerBlockEmbeddingConj.lean#L104-L133

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

theorem GlobalTheory.CompanionTheory.TyFin.ColStep.Conj.conj_mem {d j : ℕ} (hj : j ≤ d) (g : GL (Fin j) K) (h : GL (Fin d) K)
    (h1 : (h : Matrix (Fin d) (Fin d) K) = blkEmb K d j (g : Matrix (Fin j) (Fin j) K))
    (h2 : ((h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      blkEmb K d j ((g⁻¹ : GL (Fin j) K) : Matrix (Fin j) (Fin j) K))
    {u : GL (Fin d) K} (hu : u ∈ patSet K (colGe d j)) :
    h * u * h⁻¹ ∈ patSet K (colGe d j) := by sorry
