-- Prove2me | Theorems.Thm_GlobalTheory_JetConj_JetRel_comp_mul
-- name    : GlobalTheory.JetConj.JetRel.comp_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:34.240219+00:00
-- url     : https://prove2.me/theorems/c8460e1d-90fb-40d6-b512-b4dddb616e06
-- title:
--   Jet Rel: comp mul
-- statement:
--   The Jet Rel construction uses the comp mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/JetRelOfWeierstrassSystem.lean#L102-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/JetRelOfWeierstrassSystem.lean#L102-L109

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_JetRelOfWeierstrassSystem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.JetConj
variable {S : Subring (ℂ × ℂ)} {f f' g g' h h' : ℂ → ℂ}

theorem GlobalTheory.JetConj.JetRel.comp_mul (hf : Differentiable ℂ f) (hf' : Differentiable ℂ f') {c : ℂ} (hc : (c, c) ∈ S)
    (H : JetRel S f f') : JetRel S (fun z => f (c * z)) (fun z => f' (c * z)) := by sorry
