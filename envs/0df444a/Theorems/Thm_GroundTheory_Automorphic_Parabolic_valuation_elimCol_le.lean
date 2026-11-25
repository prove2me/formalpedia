-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_valuation_elimCol_le
-- name    : GroundTheory.Automorphic.Parabolic.valuation_elimCol_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:19:42.659376+00:00
-- url     : https://prove2.me/theorems/dc4f00d1-ddc1-4261-80f9-0d5a4d78e820
-- title:
--   Parabolic: valuation elim Col le
-- statement:
--   The Parabolic construction uses the valuation elim Col le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/IwahoriFactorization.lean#L246-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/IwahoriFactorization.lean#L246-L259

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_IwahoriFactorization
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
local notation "ϖ" => ((GLnLocal.uniformizer F : 𝒪[F]) : F)

theorem GroundTheory.Automorphic.Parabolic.valuation_elimCol_le {m : ℕ} (hm : 1 ≤ m) {h : GL (Fin n) F}
    (hh : h ∈ congruenceSubgroup F n m) (a i k : Fin n) :
    valuation F (elimCol β (h : Matrix (Fin n) (Fin n) F) a i k) ≤ valuation F ϖ ^ m := by sorry
