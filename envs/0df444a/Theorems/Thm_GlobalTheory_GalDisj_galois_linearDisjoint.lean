-- Prove2me | Theorems.Thm_GlobalTheory_GalDisj_galois_linearDisjoint
-- name    : GlobalTheory.GalDisj.galois_linearDisjoint
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:41:38.862688+00:00
-- url     : https://prove2.me/theorems/244a5552-5d03-4add-8206-103ec267e318
-- title:
--   Gal Disj: galois linear Disjoint
-- statement:
--   The Gal Disj construction uses the galois linear Disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GaloisLinearDisjoint.lean#L69-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GaloisLinearDisjoint.lean#L69-L126

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_GaloisLinearDisjoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.GalDisj
open Polynomial

theorem GlobalTheory.GalDisj.galois_linearDisjoint : ∀ (k Ω D : Type) [Field k] [Field Ω] [Field D] [Algebra k Ω] [IsGalois k Ω] (o : Ω →+* D) (F : Subfield D), (∀ x : Ω, o x ∈ F ↔ x ∈ (algebraMap k Ω).range) → ∀ (m : ℕ) (x : Fin m → Ω), LinearIndependent k x → ∀ b : Fin m → D, (∀ i, b i ∈ F) → ∑ i, o (x i) * b i = 0 → ∀ i, b i = 0 := by sorry
