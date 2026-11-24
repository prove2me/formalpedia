-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Desc_sum_chi_mul_chi
-- name    : GlobalTheory.UnitLemma.Desc.sum_chi_mul_chi
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:28:26.908615+00:00
-- url     : https://prove2.me/theorems/64070bda-34a1-4ea3-b49b-35910db17c4d
-- title:
--   Desc: sum chi mul chi
-- statement:
--   The Desc construction uses the sum chi mul chi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormCharacterOnIdempotentPartOrthogonalityClasse.lean#L45-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormCharacterOnIdempotentPartOrthogonalityClasse.lean#L45-L106

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormCharacterOnIdempotentPartFramePropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormCharacterOnIdempotentPartOrthogonalityClasse
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc
open GlobalTheory.UnitLemma Polynomial Filter Topology

theorem GlobalTheory.UnitLemma.Desc.sum_chi_mul_chi {K : UQ} (B : InvAlg K) {ι : Type} [Fintype ι] [DecidableEq ι] (e π : ι → B.A)
    (S : Finset ι) (hF : IsFrame B e π S) [Fintype B.Cl] (I₀ I : Finset ι) (h₀ : I₀ ⊆ S) (hI : I ⊆ S) :
    ∑ k : B.Cl, chi B e I₀ k.rep * chi B e I k.rep = if I = I₀ then (Fintype.card B.Cl : ℚ) else 0 := by sorry
