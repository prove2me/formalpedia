-- Prove2me | Theorems.Thm_GlobalTheory_OrbitMass_toCoset_mk
-- name    : GlobalTheory.OrbitMass.toCoset_mk
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-27T05:18:27.275703+00:00
-- url     : https://prove2.me/theorems/39dfc3e7-6af5-414a-aa04-32ba5709910a
-- title:
--   Orbit Mass: to Coset mk
-- statement:
--   The Orbit Mass construction uses the to Coset mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OrbitMassFormulaFiniteIndexSubgroup.lean#L29-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OrbitMassFormulaFiniteIndexSubgroup.lean#L29-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrbitMassFormulaFiniteIndexSubgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MulAction
open GlobalTheory GlobalTheory.OrbitMass
variable {G H D : Type} [Group G] [Group H] [MulAction G D] [MulAction H D]

theorem GlobalTheory.OrbitMass.toCoset_mk (ι : H →* G) (hc : ∀ (h : H) (d : D), ι h • d = h • d) (x : D) (g : G) :
    toCoset ι hc x (g : G ⧸ ι.range) = Quotient.mk'' (g⁻¹ • x) := by sorry
