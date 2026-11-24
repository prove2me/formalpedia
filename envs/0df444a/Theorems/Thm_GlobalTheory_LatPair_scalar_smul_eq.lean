-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_scalar_smul_eq
-- name    : GlobalTheory.LatPair.scalar_smul_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:58:39.293788+00:00
-- url     : https://prove2.me/theorems/f1e1a23a-c7db-4329-ad33-3bbc87a66944
-- title:
--   Lat Pair: scalar smul eq
-- statement:
--   The Lat Pair construction uses the scalar smul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L628-L638
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean#L628-L638

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

theorem GlobalTheory.LatPair.scalar_smul_eq [Fintype n] [DecidableEq n] (g : GL n k) (s : 𝒪[k]ˣ) (hg : ∀ x : n → k, g • x = (s : 𝒪[k]) • x)
    (P : Pair k n) : g • P = (Units.map (residue 𝒪[k]).toMonoidHom s)⁻¹ • P := by sorry
