-- Prove2me | Theorems.Thm_GlobalTheory_T_cocycle_vanishing_on_fixingSubgroup_determined_by_generator
-- name    : GlobalTheory.T.cocycle_vanishing_on_fixingSubgroup_determined_by_generator
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:47:16.486142+00:00
-- url     : https://prove2.me/theorems/9399370e-0abf-5c19-8626-efe7f49c9664
-- title:
--   T: cocycle vanishing on fixing Subgroup determined by generator
-- statement:
--   The T construction uses the cocycle vanishing on fixing Subgroup determined by generator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CocycleVanishingOnFixingSubgroupDeterminedByGeneStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CocycleVanishingOnFixingSubgroupDeterminedByGeneStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CocycleVanishingOnFixingSubgroupDeterminedByGene
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CocycleVanishingOnFixingSubgroupDeterminedByGeneStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.cocycle_vanishing_on_fixingSubgroup_determined_by_generator : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ (m r : ℕ), Lev l m → ∀ (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (g : GQ l), Frame χ K m U g → ∀ i : ℤ, (∀ c : GQ l → Fin r → PadicComplex l, CocOn (Gj K m) (twAct act χ i U) Set.univ c → (∀ h ∈ Hinf K, c h = 0) → c g = 0 → ∀ σ ∈ Gj K m, c σ = 0) ∧ ∀ w : Fin r → PadicComplex l, (∀ a, w a ∈ Ohat K) → ∃ c : GQ l → Fin r → PadicComplex l, CocOn (Gj K m) (twAct act χ i U) {y | ∀ a, y a ∈ Ohat K} c ∧ (∀ h ∈ Hinf K, c h = 0) ∧ c g = w := by sorry
