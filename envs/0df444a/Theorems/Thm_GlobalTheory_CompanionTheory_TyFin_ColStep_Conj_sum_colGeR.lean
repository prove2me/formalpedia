-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_ColStep_Conj_sum_colGeR
-- name    : GlobalTheory.CompanionTheory.TyFin.ColStep.Conj.sum_colGeR
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:17:32.564923+00:00
-- url     : https://prove2.me/theorems/7a22ab3d-4bba-4ad4-b149-5048640fdddf
-- title:
--   Conj: sum col Ge R
-- statement:
--   The Conj construction uses the sum col Ge R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WhittakerBlockEmbeddingConj.lean#L135-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WhittakerBlockEmbeddingConj.lean#L135-L153

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

theorem GlobalTheory.CompanionTheory.TyFin.ColStep.Conj.sum_colGeR {d j : ℕ} (hj : j < d) (r : Fin j → K) (M : Matrix (Fin d) (Fin d) K) :
    ∑ i, ∑ l, colGeR K d j r i l * M i l =
      ∑ i, ∑ l, colGeE K d (j + 1) i l * M i l +
        ∑ k : Fin j, r k * M (Fin.castLE hj.le k) ⟨j, hj⟩ := by sorry
