-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_Pair_exists_le_le
-- name    : GlobalTheory.CechDR.Pair.exists_le_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:59:29.765703+00:00
-- url     : https://prove2.me/theorems/1700194e-f481-4af0-913d-510e94fa6e5b
-- title:
--   Pair: exists le le
-- statement:
--   The Pair construction uses the exists le le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsBasicOpen.lean#L22-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsBasicOpen.lean#L22-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBasicOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry
open GlobalTheory GlobalTheory.CechDR
variable {X X' : Scheme.{0}}

theorem GlobalTheory.CechDR.Pair.exists_le_le (φ : X' ⟶ X) (p q : Pair φ) {x : X'} (hx : x ∈ p.1.1.1 ⊓ q.1.1.1) :
    ∃ r : Pair φ, r ≤ p ∧ r ≤ q ∧ x ∈ r.1.1.1 := by sorry
