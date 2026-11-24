-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_map_mem_EqForm
-- name    : GlobalTheory.LatPair.map_mem_EqForm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:36:59.344098+00:00
-- url     : https://prove2.me/theorems/9178a0bc-3bb6-42c2-b6b1-c703db52fd9f
-- title:
--   Lat Pair: map mem Eq Form
-- statement:
--   The Lat Pair construction uses the map mem Eq Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L219-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L219-L224

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.LatPair
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
variable (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (φ : Form k n M)
variable [Fintype n] [DecidableEq n]
variable (π : Representation ℂ (GL n k) M)

theorem GlobalTheory.LatPair.map_mem_EqForm {T : Module.End ℂ (Form k n M)}
    (h1 : ∀ (g : GL n k) φ P, T φ (g • P) = T (fun Q => φ (g • Q)) P)
    (h2 : ∀ (g : GL n k) (φ : Form k n M) P, T (fun Q => π g (φ Q)) P = π g (T φ P))
    {φ : Form k n M} (h : φ ∈ EqForm π) : T φ ∈ EqForm π := by sorry
