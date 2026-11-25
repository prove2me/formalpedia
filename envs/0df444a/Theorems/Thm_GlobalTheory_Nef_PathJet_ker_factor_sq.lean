-- Prove2me | Theorems.Thm_GlobalTheory_Nef_PathJet_ker_factor_sq
-- name    : GlobalTheory.Nef.PathJet.ker_factor_sq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:08:31.165498+00:00
-- url     : https://prove2.me/theorems/77350bb5-6a27-4446-9d6e-543fadd14dc9
-- title:
--   Path Jet: ker factor sq
-- statement:
--   The Path Jet construction uses the ker factor sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIsRingHomModXPowSuccLift.lean#L43-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIsRingHomModXPowSuccLift.lean#L43-L60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DerivCompM
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIsRingHomModXPowSuccLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.Nef
open GlobalTheory GlobalTheory.Nef GlobalTheory.Nef.PathJet
open PowerSeries

theorem GlobalTheory.Nef.PathJet.ker_factor_sq {R : Type} [CommRing R] (n : ℕ) (hn : 1 ≤ n)
    (hle : Ideal.span {(X : PowerSeries R) ^ (n + 1)} ≤ Ideal.span {(X : PowerSeries R) ^ n}) :
    RingHom.ker (Ideal.Quotient.factor hle) ^ 2 = ⊥ := by sorry
