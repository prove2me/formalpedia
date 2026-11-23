-- Prove2me | Theorems.Thm_GlobalTheory_PadicH2Separated_toZModPow_eq_iff
-- name    : GlobalTheory.PadicH2Separated.toZModPow_eq_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:56.721915+00:00
-- url     : https://prove2.me/theorems/65906cd2-8a17-4290-9f76-8e9eb92ea4a1
-- title:
--   Padic H2 Separated: to ZMod Pow eq iff
-- statement:
--   The Padic H2 Separated construction uses the to ZMod Pow eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PadicCoboundaryOfDivisible.lean#L7-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PadicCoboundaryOfDivisible.lean#L7-L10

import Mathlib
import Definitions.Def_Formalism_GaloisCohomology_LocalTateDualityK
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicCoboundaryOfDivisible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology
open GlobalTheory GlobalTheory.PadicH2Separated

theorem GlobalTheory.PadicH2Separated.toZModPow_eq_iff {l : ℕ} [Fact l.Prime] (r : ℕ) (x y : ℤ_[l]) :
    PadicInt.toZModPow r x = PadicInt.toZModPow r y ↔ ‖x - y‖ ≤ (l : ℝ) ^ (-(r : ℤ)) := by sorry
