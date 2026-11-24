-- Prove2me | Theorems.Thm_GlobalTheory_RealAlgebraCharacters_realAlg_sep
-- name    : GlobalTheory.RealAlgebraCharacters.realAlg_sep
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:15:07.129691+00:00
-- url     : https://prove2.me/theorems/fc692f04-0465-434e-afbe-aaf6868cf557
-- title:
--   Real Algebra Characters: real Alg sep
-- statement:
--   The Real Algebra Characters construction uses the real Alg sep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RealAlgSep.lean#L91-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RealAlgSep.lean#L91-L122

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RealAlgSep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.RealAlgebraCharacters
open Filter Topology
variable {X : Type} {B : Type} [AddCommGroup B] (χ : B → X → ℂ)

theorem GlobalTheory.RealAlgebraCharacters.realAlg_sep [TopologicalSpace X] (hc : ∀ b, Continuous (χ b))
    (hadd : ∀ (a b : B) (x : X), χ (a + b) x = χ a x * χ b x)
    (h0 : ∀ x, χ 0 x = 1) (hn : ∀ (a : B) (x : X), ‖χ a x‖ = 1)
    (hs : ∀ x y : X, x ≠ y → ∃ b, χ b x ≠ χ b y) : (realAlg χ hadd h0).SeparatesPoints := by sorry
