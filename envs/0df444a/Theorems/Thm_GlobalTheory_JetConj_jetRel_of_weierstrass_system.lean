-- Prove2me | Theorems.Thm_GlobalTheory_JetConj_jetRel_of_weierstrass_system
-- name    : GlobalTheory.JetConj.jetRel_of_weierstrass_system
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:39:21.107632+00:00
-- url     : https://prove2.me/theorems/86cbd68f-1676-405b-b7cf-12f54f42c20f
-- title:
--   Jet Conj: jet Rel of weierstrass system
-- statement:
--   The Jet Conj construction uses the jet Rel of weierstrass system property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/JetRelOfWeierstrassSystem.lean#L221-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/JetRelOfWeierstrassSystem.lean#L221-L253

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

theorem GlobalTheory.JetConj.jetRel_of_weierstrass_system {p q p' q' : ℂ → ℂ} {c c' : ℂ} (hc : (c, c') ∈ S)
    (hp : AnalyticAt ℂ p 0) (hp' : AnalyticAt ℂ p' 0) (hq : AnalyticAt ℂ q 0) (hq' : AnalyticAt ℂ q' 0)
    (e1 : deriv p =ᶠ[𝓝 0] q) (e1' : deriv p' =ᶠ[𝓝 0] q')
    (e2 : deriv q =ᶠ[𝓝 0] fun z => (6 * p z) * p z - c)
    (e2' : deriv q' =ᶠ[𝓝 0] fun z => (6 * p' z) * p' z - c')
    (h0 : (p 0, p' 0) ∈ S) (h1 : (q 0, q' 0) ∈ S) : JetRel S q q' := by sorry
