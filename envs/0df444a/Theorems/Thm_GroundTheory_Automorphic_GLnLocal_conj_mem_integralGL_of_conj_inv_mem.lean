-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GLnLocal_conj_mem_integralGL_of_conj_inv_mem
-- name    : GroundTheory.Automorphic.GLnLocal.conj_mem_integralGL_of_conj_inv_mem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:29:52.067279+00:00
-- url     : https://prove2.me/theorems/8dcceecb-9f4d-493f-ba27-a57081c9b4e0
-- title:
--   GLn Local: conj mem integral GL of conj inv mem
-- statement:
--   The GLn Local construction uses the conj mem integral GL of conj inv mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GLnLattice.lean#L178-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GLnLattice.lean#L178-L273

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
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
open ValuativeRel Topology Filter Set
open scoped Pointwise Matrix
open GroundTheory.Automorphic.GLnLocal
variable (F : Type*) [Field F] [ValuativeRel F] (n : ℕ)

theorem GroundTheory.Automorphic.GLnLocal.conj_mem_integralGL_of_conj_inv_mem {g : GL (Fin n) F}
    (hg : ∀ k ∈ integralGL F n, g⁻¹ * k * g ∈ integralGL F n) {k : GL (Fin n) F}
    (hk : k ∈ integralGL F n) : g * k * g⁻¹ ∈ integralGL F n := by sorry
