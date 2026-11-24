-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_pair_glue
-- name    : GlobalTheory.CechDR.pair_glue
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:59:28.365859+00:00
-- url     : https://prove2.me/theorems/9c15e3fa-3251-475e-bc28-24282f38d349
-- title:
--   Cech DR: pair glue
-- statement:
--   The Cech DR construction uses the pair glue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsGlueFunctionsAffineOpenFromPairs.lean#L9-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsGlueFunctionsAffineOpenFromPairs.lean#L9-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBasicOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGlueFunctionsAffineOpenFromPairs
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
open GlobalTheory GlobalTheory.CechDR

theorem GlobalTheory.CechDR.pair_glue : ∀ {R' : Type} [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X) (s' : X' ⟶ Sp R')
    (W : X'.affineOpens) (k : ∀ p : Pair φ, p.1.1 ≤ W → (OAff s').obj (op p.1.1)),
    (∀ (p q : Pair φ) (hp : p.1.1 ≤ W) (hq : q.1.1 ≤ W) (hqp : q ≤ p),
      mp (OAff s') (homOfLE (Pair.le_fst hqp)).op (k p hp) = k q hq) →
    ∃ G : (OAff s').obj (op W), ∀ (p : Pair φ) (hp : p.1.1 ≤ W), mp (OAff s') (homOfLE hp).op G = k p hp := by sorry
