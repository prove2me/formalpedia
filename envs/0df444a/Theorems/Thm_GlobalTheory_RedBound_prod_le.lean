-- Prove2me | Theorems.Thm_GlobalTheory_RedBound_prod_le
-- name    : GlobalTheory.RedBound.prod_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:18:39.498139+00:00
-- url     : https://prove2.me/theorems/b095e164-e167-4b1f-9e19-e879752ed0c8
-- title:
--   Red Bound: prod le
-- statement:
--   The Red Bound construction uses the prod le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SiegelReducedIntegralFormBoundedEntries.lean#L40-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SiegelReducedIntegralFormBoundedEntries.lean#L40-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_UnipotentUpperInvUpperTriangularBoundedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SiegelReducedIntegralFormBoundedEntries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open GlobalTheory GlobalTheory.RedBound

theorem GlobalTheory.RedBound.prod_le {N : ℕ} {C Cm : ℝ} {k : Matrix (Fin N) (Fin N) ℝ} {a : Fin N → ℝ}
    {n : Matrix (Fin N) (Fin N) ℝ} (hS : IsSiegel C k a n) (h1 : 1 ≤ Cm) (hC : C ≤ Cm)
    {p q r s : Fin N} (hr : p ≤ r) (hs : q ≤ s) : a p * a q ≤ Cm ^ 2 * (a r * a s) := by sorry
