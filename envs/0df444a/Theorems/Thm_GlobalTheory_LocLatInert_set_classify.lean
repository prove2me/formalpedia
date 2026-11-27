-- Prove2me | Theorems.Thm_GlobalTheory_LocLatInert_set_classify
-- name    : GlobalTheory.LocLatInert.set_classify
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-27T05:48:43.131123+00:00
-- url     : https://prove2.me/theorems/35d2b14e-2116-5fb4-a949-1d30bb45f59d
-- title:
--   Loc Lat Inert: set classify
-- statement:
--   The Loc Lat Inert construction uses the set classify property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StableLatticeEqZpowStdInertCompletion.lean#L150-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StableLatticeEqZpowStdInertCompletion.lean#L150-L180

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StableLatticeEqZpowStdInertCompletion
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain NumberField
open scoped Matrix
open GlobalTheory GlobalTheory.LocLatInert
variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]

theorem GlobalTheory.LocLatInert.set_classify (I : Set K) (hmul : ∀ a : K, Valued.v a ≤ 1 → ∀ t ∈ I, a * t ∈ I)
    (N : K) (hN : N ≠ 0) (hNI : N ∈ I) (hb : ∀ t ∈ I, Valued.v (N * t) ≤ 1) :
    ∃ M : ℤ, ∀ t, t ∈ I ↔ Valued.v t ≤ WithZero.exp M := by sorry
