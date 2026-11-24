-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_Pair_exists_basicOpen
-- name    : GlobalTheory.CechDR.Pair.exists_basicOpen
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:13:59.051884+00:00
-- url     : https://prove2.me/theorems/91782e6c-9f94-4c58-bb8c-b71163e0d144
-- title:
--   Pair: exists basic Open
-- statement:
--   The Pair construction uses the exists basic Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsBasicOpen.lean#L15-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsBasicOpen.lean#L15-L20

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

theorem GlobalTheory.CechDR.Pair.exists_basicOpen (φ : X' ⟶ X) (W : X'.affineOpens) {x : X'} (hx : x ∈ W.1) :
    ∃ (p : Pair φ) (f : Γ(X', W.1)), p.1.1.1 = X'.basicOpen f ∧ x ∈ p.1.1.1 := by sorry
