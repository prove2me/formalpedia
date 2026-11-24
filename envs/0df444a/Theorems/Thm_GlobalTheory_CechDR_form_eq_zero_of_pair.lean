-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_form_eq_zero_of_pair
-- name    : GlobalTheory.CechDR.form_eq_zero_of_pair
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:01:38.075838+00:00
-- url     : https://prove2.me/theorems/37b2b7a5-5773-436c-b3d9-a34e7ec994d9
-- title:
--   Cech DR: form eq zero of pair
-- statement:
--   The Cech DR construction uses the form eq zero of pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OneFormEqZeroOfVanishingOnPairs.lean#L31-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OneFormEqZeroOfVanishingOnPairs.lean#L31-L56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBasicOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneFormEqZeroOfVanishingOnPairs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR Opposite KaehlerDifferential
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CechDR

theorem GlobalTheory.CechDR.form_eq_zero_of_pair {R' : Type} [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X)
    (s' : X' ⟶ Sp R') (W : X'.affineOpens) (ω : Ω[(OAff s').obj (op W)⁄R'])
    (h : ∀ (p : Pair φ) (hp : p.1.1 ≤ W), p1 (OAff s') (homOfLE hp).op ω = 0) : ω = 0 := by sorry
