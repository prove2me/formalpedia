-- Prove2me | Theorems.Thm_GlobalTheory_AffGlue_Cech_eq_zero_of_small
-- name    : GlobalTheory.AffGlue.Cech.eq_zero_of_small
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:47:58.935948+00:00
-- url     : https://prove2.me/theorems/2083f8fd-436e-47dc-b400-25a784ffcf70
-- title:
--   Cech: eq zero of small
-- statement:
--   The Cech construction uses the eq zero of small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AffineCoverSectionsGlue.lean#L21-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AffineCoverSectionsGlue.lean#L21-L30

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

theorem GlobalTheory.AffGlue.Cech.eq_zero_of_small (D : Data T) {V : T.Opens} (hV : IsAffineOpen V) {ι : Type}
    (W : ι → T.Opens) (hc : V ≤ ⨆ i, W i) (x : D.M V hV)
    (hx : ∀ (i : ι) (O : T.Opens) (hO : IsAffineOpen O) (h : O ≤ V), O ≤ W i →
      D.ρ hV hO h x = 0) : x = 0 := by sorry
