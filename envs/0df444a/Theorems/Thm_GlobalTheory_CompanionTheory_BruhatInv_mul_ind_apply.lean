-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BruhatInv_mul_ind_apply
-- name    : GlobalTheory.CompanionTheory.BruhatInv.mul_ind_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:09:09.984505+00:00
-- url     : https://prove2.me/theorems/cd21195f-1701-4777-bbda-ea16a6739f6d
-- title:
--   Bruhat Inv: mul ind apply
-- statement:
--   The Bruhat Inv construction uses the mul ind apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BruhatDecompositionUnique.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BruhatDecompositionUnique.lean#L20-L22

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

theorem GlobalTheory.CompanionTheory.BruhatInv.mul_ind_apply (p : ι → Prop) [DecidablePred p] (A : Matrix ι ι K) (i j : ι) :
    (A * ind K p) i j = A i j * (if p j then 1 else 0) := by sorry
