-- Prove2me | Theorems.Thm_GlobalTheory_UnitPairNorm_main
-- name    : GlobalTheory.UnitPairNorm.main
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:39:17.855266+00:00
-- url     : https://prove2.me/theorems/4da31a18-c19e-4f05-a75f-e664f4968b0d
-- title:
--   Unit Pair Norm: main
-- statement:
--   The Unit Pair Norm construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnitNorm.lean#L292-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnitNorm.lean#L292-L295

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitPairNorm
open Module

theorem GlobalTheory.UnitPairNorm.main : ∀ (K : GlobalTheory.UnitLemma.UQ), (∀ (u : (GlobalTheory.UnitLemma.UQ.O K)ˣ), (GlobalTheory.UnitLemma.UQ.c K : GlobalTheory.UnitLemma.UQ.E K → GlobalTheory.UnitLemma.UQ.E K) ((Algebra.algebraMap (GlobalTheory.UnitLemma.UQ.O K) (GlobalTheory.UnitLemma.UQ.E K) : GlobalTheory.UnitLemma.UQ.O K → GlobalTheory.UnitLemma.UQ.E K) (↑u : GlobalTheory.UnitLemma.UQ.O K)) = (Algebra.algebraMap (GlobalTheory.UnitLemma.UQ.O K) (GlobalTheory.UnitLemma.UQ.E K) : GlobalTheory.UnitLemma.UQ.O K → GlobalTheory.UnitLemma.UQ.E K) (↑u : GlobalTheory.UnitLemma.UQ.O K) → ∃ (z : (GlobalTheory.UnitLemma.UQ.O K)ˣ), (Algebra.algebraMap (GlobalTheory.UnitLemma.UQ.O K) (GlobalTheory.UnitLemma.UQ.E K) : GlobalTheory.UnitLemma.UQ.O K → GlobalTheory.UnitLemma.UQ.E K) (↑u : GlobalTheory.UnitLemma.UQ.O K) = (Algebra.algebraMap (GlobalTheory.UnitLemma.UQ.O K) (GlobalTheory.UnitLemma.UQ.E K) : GlobalTheory.UnitLemma.UQ.O K → GlobalTheory.UnitLemma.UQ.E K) (↑z : GlobalTheory.UnitLemma.UQ.O K) * (GlobalTheory.UnitLemma.UQ.c K : GlobalTheory.UnitLemma.UQ.E K → GlobalTheory.UnitLemma.UQ.E K) ((Algebra.algebraMap (GlobalTheory.UnitLemma.UQ.O K) (GlobalTheory.UnitLemma.UQ.E K) : GlobalTheory.UnitLemma.UQ.O K → GlobalTheory.UnitLemma.UQ.E K) (↑z : GlobalTheory.UnitLemma.UQ.O K))) → (∃ (z : GlobalTheory.UnitLemma.UQ.O K), (Algebra.algebraMap (GlobalTheory.UnitLemma.UQ.O K) (GlobalTheory.UnitLemma.UQ.E K) : GlobalTheory.UnitLemma.UQ.O K → GlobalTheory.UnitLemma.UQ.E K) z + (GlobalTheory.UnitLemma.UQ.c K : GlobalTheory.UnitLemma.UQ.E K → GlobalTheory.UnitLemma.UQ.E K) ((Algebra.algebraMap (GlobalTheory.UnitLemma.UQ.O K) (GlobalTheory.UnitLemma.UQ.E K) : GlobalTheory.UnitLemma.UQ.O K → GlobalTheory.UnitLemma.UQ.E K) z) = (1 : GlobalTheory.UnitLemma.UQ.E K)) → ∀ (n : ℕ) (V : Type) [inst : AddCommGroup V] [inst_1 : Module (GlobalTheory.UnitLemma.UQ.E K) V] [inst_2 : Module (GlobalTheory.UnitLemma.UQ.O K) V] [IsScalarTower (GlobalTheory.UnitLemma.UQ.O K) (GlobalTheory.UnitLemma.UQ.E K) V] [Module.Finite (GlobalTheory.UnitLemma.UQ.E K) V] (h : V → V → GlobalTheory.UnitLemma.UQ.E K), Module.finrank (GlobalTheory.UnitLemma.UQ.E K) V = n → (∀ (x y z : V), h (x + y) z = h x z + h y z) → (∀ (c : GlobalTheory.UnitLemma.UQ.E K) (x z : V), h (c • x) z = c * h x z) → (∀ (x y : V), h y x = (GlobalTheory.UnitLemma.UQ.c K : GlobalTheory.UnitLemma.UQ.E K → GlobalTheory.UnitLemma.UQ.E K) (h x y)) → ∀ (L : Submodule (GlobalTheory.UnitLemma.UQ.O K) V), Submodule.FG L → Submodule.span (GlobalTheory.UnitLemma.UQ.E K) (↑L : Set V) = ⊤ → (∀ (y : V), y ∈ L ↔ ∀ z ∈ L, h y z ∈ RingHom.range (Algebra.algebraMap (GlobalTheory.UnitLemma.UQ.O K) (GlobalTheory.UnitLemma.UQ.E K))) → ∃ (m : ℕ) (v : Fin m → V), (∀ (i j : Fin m), h (v i) (v j) = if i = j then (1 : GlobalTheory.UnitLemma.UQ.E K) else (0 : GlobalTheory.UnitLemma.UQ.E K)) ∧ Submodule.span (GlobalTheory.UnitLemma.UQ.O K) (Set.range v) = L := by sorry
