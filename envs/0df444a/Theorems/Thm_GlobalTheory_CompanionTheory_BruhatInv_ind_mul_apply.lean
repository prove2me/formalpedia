-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BruhatInv_ind_mul_apply
-- name    : GlobalTheory.CompanionTheory.BruhatInv.ind_mul_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:09:15.835003+00:00
-- url     : https://prove2.me/theorems/9f2fe24f-e5db-4e17-83d2-0a94489a297a
-- title:
--   Bruhat Inv: ind mul apply
-- statement:
--   The Bruhat Inv construction uses the ind mul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BruhatDecompositionUnique.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BruhatDecompositionUnique.lean#L16-L18

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BruhatDecompositionUnique
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin Formalism.IrreducibleCountingLemmas.TYPES
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BruhatInv
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.CompanionTheory.BruhatInv.ind_mul_apply (p : ι → Prop) [DecidablePred p] (A : Matrix ι ι K) (i j : ι) :
    (ind K p * A) i j = (if p i then 1 else 0) * A i j := by sorry
