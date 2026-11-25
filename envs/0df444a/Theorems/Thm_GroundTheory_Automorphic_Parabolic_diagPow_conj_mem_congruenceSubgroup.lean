-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_diagPow_conj_mem_congruenceSubgroup
-- name    : GroundTheory.Automorphic.Parabolic.diagPow_conj_mem_congruenceSubgroup
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:44:47.673093+00:00
-- url     : https://prove2.me/theorems/f28bcc6c-c0fa-5687-b425-88a885cf55eb
-- title:
--   Parabolic: diag Pow conj mem congruence Subgroup
-- statement:
--   The Parabolic construction uses the diag Pow conj mem congruence Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalAdmissible.lean#L101-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalAdmissible.lean#L101-L135

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LeviCartan
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
open Cartan

theorem GroundTheory.Automorphic.Parabolic.diagPow_conj_mem_congruenceSubgroup {μ : Fin n → ℤ} {u : GL (Fin n) F} {t m : ℕ}
    {C : ℤ} (hC : ((t + m : ℕ) : ℤ) < C)
    (hu : ∀ i j, u i j = (1 : Matrix (Fin n) (Fin n) F) i j ∨ μ j + C ≤ μ i)
    (hu' : ∀ i j, (u⁻¹ : GL (Fin n) F) i j = (1 : Matrix (Fin n) (Fin n) F) i j ∨ μ j + C ≤ μ i)
    (hb : ∀ i j, (uniformizer F : F) ^ t * u i j ∈ 𝒪[F])
    (hb' : ∀ i j, (uniformizer F : F) ^ t * (u⁻¹ : GL (Fin n) F) i j ∈ 𝒪[F]) :
    diagPow F n μ * u * (diagPow F n μ)⁻¹ ∈ congruenceSubgroup F n m := by sorry
