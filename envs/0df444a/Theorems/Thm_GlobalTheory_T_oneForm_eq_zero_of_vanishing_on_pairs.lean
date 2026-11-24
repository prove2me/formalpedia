-- Prove2me | Theorems.Thm_GlobalTheory_T_oneForm_eq_zero_of_vanishing_on_pairs
-- name    : GlobalTheory.T.oneForm_eq_zero_of_vanishing_on_pairs
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:55:33.451283+00:00
-- url     : https://prove2.me/theorems/57b542dd-95d8-456e-ba57-f898ea5f6541
-- title:
--   T: one Form eq zero of vanishing on pairs
-- statement:
--   The T construction uses the one Form eq zero of vanishing on pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OneFormEqZeroOfVanishingOnPairsStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OneFormEqZeroOfVanishingOnPairsStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneFormEqZeroOfVanishingOnPairs
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBasicOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneFormEqZeroOfVanishingOnPairsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR Opposite KaehlerDifferential
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.oneForm_eq_zero_of_vanishing_on_pairs : ∀ {R' : Type} [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X) (s' : X' ⟶ Sp R') (W : X'.affineOpens) (ω : Ω[(OAff s').obj (op W)⁄R']), (∀ (p : Pair φ) (hp : p.1.1 ≤ W), p1 (OAff s') (homOfLE hp).op ω = 0) → ω = 0 := by sorry
