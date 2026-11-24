-- Prove2me | Theorems.Thm_GlobalTheory_AuxiliaryLemmaFirst_main
-- name    : GlobalTheory.AuxiliaryLemmaFirst.main
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:57:57.290649+00:00
-- url     : https://prove2.me/theorems/6ab1f3f5-fc62-492c-a9fe-992da3c12fc3
-- title:
--   Auxiliary Lemma First: main
-- statement:
--   The Auxiliary Lemma First construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ImportsMoreSide.lean#L7-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ImportsMoreSide.lean#L7-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsMoreSide
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct KaehlerDifferential
open GlobalTheory GlobalTheory.AuxiliaryLemmaFirst

theorem GlobalTheory.AuxiliaryLemmaFirst.main : ∀ (R R' B C B' K : Type) [inst : CommRing R] [inst_1 : CommRing R'] [inst_2 : CommRing B] [inst_3 : CommRing C] [inst_4 : CommRing B'] [inst_5 : Field K] [inst_6 : Algebra R R'] [inst_7 : Algebra R B] [inst_8 : Algebra R C] [inst_9 : Algebra R' C] [inst_10 : Algebra B C] [inst_11 : IsScalarTower R R' C] [inst_12 : IsScalarTower R B C] [Algebra.IsPushout R R' B C] [inst_14 : Algebra C B'] [inst_15 : Algebra R' B'] [IsScalarTower R' C B'] [Algebra.FormallyEtale C B'] [inst_18 : Algebra B' K] [inst_19 : Algebra B K], (∀ (x : B), (Algebra.algebraMap B K : B → K) x = (Algebra.algebraMap B' K : B' → K) ((Algebra.algebraMap C B' : C → B') ((Algebra.algebraMap B C : B → C) x))) → ∃ (e : TensorProduct B K Ω[B⁄R] ≃ₗ[K] TensorProduct B' K Ω[B'⁄R']), ∀ (x : B), (e : TensorProduct B K Ω[B⁄R] → TensorProduct B' K Ω[B'⁄R']) ((1 : K) ⊗ₜ[B] (KaehlerDifferential.D R B : B → Ω[B⁄R]) x) = (1 : K) ⊗ₜ[B'] (KaehlerDifferential.D R' B' : B' → Ω[B'⁄R']) ((Algebra.algebraMap C B' : C → B') ((Algebra.algebraMap B C : B → C) x)) := by sorry
