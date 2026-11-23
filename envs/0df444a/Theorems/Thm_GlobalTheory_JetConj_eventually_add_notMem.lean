-- Prove2me | Theorems.Thm_GlobalTheory_JetConj_eventually_add_notMem
-- name    : GlobalTheory.JetConj.eventually_add_notMem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:13.676368+00:00
-- url     : https://prove2.me/theorems/6d28e51c-8caa-4f9a-b870-2cc64a043ca9
-- title:
--   Jet Conj: eventually add not Mem
-- statement:
--   The Jet Conj construction uses the eventually add not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SecondDerivSigmaProductAtZero.lean#L123-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SecondDerivSigmaProductAtZero.lean#L123-L125

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_JetRelOfWeierstrassSystem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SecondDerivSigmaProductAtZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology PeriodPair
open GlobalTheory GlobalTheory.JetConj
variable {L : PeriodPair} {σ : ℂ → ℂ}

theorem GlobalTheory.JetConj.eventually_add_notMem (L : PeriodPair) {u z : ℂ} (hz : z + u ∉ L.lattice) :
    ∀ᶠ w in 𝓝 z, w + u ∉ L.lattice := by sorry
