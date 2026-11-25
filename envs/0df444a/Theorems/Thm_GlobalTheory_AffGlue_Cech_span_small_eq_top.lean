-- Prove2me | Theorems.Thm_GlobalTheory_AffGlue_Cech_span_small_eq_top
-- name    : GlobalTheory.AffGlue.Cech.span_small_eq_top
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:48:23.668844+00:00
-- url     : https://prove2.me/theorems/1d45b5c1-8ff7-43ce-9233-6536a504cc6e
-- title:
--   Cech: span small eq top
-- statement:
--   The Cech construction uses the span small eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AffineCoverSectionsGlue.lean#L12-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AffineCoverSectionsGlue.lean#L12-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SecEquivResM
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AffineCoverSectionsGlue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AffGlue
open GlobalTheory GlobalTheory.AffGlue GlobalTheory.AffGlue.Cech
variable {T : Scheme.{0}}

theorem GlobalTheory.AffGlue.Cech.span_small_eq_top {V : T.Opens} (hV : IsAffineOpen V) {ι : Type} (W : ι → T.Opens)
    (hc : V ≤ ⨆ i, W i) :
    Ideal.span {f : Γ(T, V) | ∃ i, T.basicOpen f ≤ W i} = ⊤ := by sorry
