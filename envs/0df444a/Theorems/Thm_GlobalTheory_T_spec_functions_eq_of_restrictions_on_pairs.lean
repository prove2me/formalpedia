-- Prove2me | Theorems.Thm_GlobalTheory_T_spec_functions_eq_of_restrictions_on_pairs
-- name    : GlobalTheory.T.spec_functions_eq_of_restrictions_on_pairs
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:58:23.561565+00:00
-- url     : https://prove2.me/theorems/04322072-bd3a-4d9d-a477-7af12b303981
-- title:
--   T: spec functions eq of restrictions on pairs
-- statement:
--   The T construction uses the spec functions eq of restrictions on pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpecFunctionsEqOfRestrictionsOnPairsStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpecFunctionsEqOfRestrictionsOnPairsStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpecFunctionsEqOfRestrictionsOnPairs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SecPullA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpecFunctionsEqOfRestrictionsOnPairsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechDR.AffLoc
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.spec_functions_eq_of_restrictions_on_pairs : ∀ {X : Scheme.{0}} (B B' : Type) [CommRing B] [CommRing B'] (x : Sp B ⟶ X) (ψ : Sp B' ⟶ Sp B) (a b : B'), (∀ (V' : (Sp B').affineOpens) (p : Pair x), V'.1 ≤ ψ ⁻¹ᵁ p.1.1.1 → (secMap (𝟙 (Sp B')) V'.1).hom a = (secMap (𝟙 (Sp B')) V'.1).hom b) → a = b := by sorry
