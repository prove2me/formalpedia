-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_glue_functions_affineOpen_from_pairs
-- name    : GlobalTheory.T.exists_glue_functions_affineOpen_from_pairs
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:36:48.633653+00:00
-- url     : https://prove2.me/theorems/514591cd-ab2f-45df-a406-af9386d81ec3
-- title:
--   T: exists glue functions affine Open from pairs
-- statement:
--   The T construction uses the exists glue functions affine Open from pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsGlueFunctionsAffineOpenFromPairsStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsGlueFunctionsAffineOpenFromPairsStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGlueFunctionsAffineOpenFromPairs
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBasicOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGlueFunctionsAffineOpenFromPairsStatement
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

theorem GlobalTheory.T.exists_glue_functions_affineOpen_from_pairs : ∀ {R' : Type} [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X) (s' : X' ⟶ Sp R') (W : X'.affineOpens) (k : ∀ p : Pair φ, p.1.1 ≤ W → (OAff s').obj (op p.1.1)), (∀ (p q : Pair φ) (hp : p.1.1 ≤ W) (hq : q.1.1 ≤ W) (hqp : q ≤ p), mp (OAff s') (homOfLE (Pair.le_fst hqp)).op (k p hp) = k q hq) → ∃ G : (OAff s').obj (op W), ∀ (p : Pair φ) (hp : p.1.1 ≤ W), mp (OAff s') (homOfLE hp).op G = k p hp := by sorry
