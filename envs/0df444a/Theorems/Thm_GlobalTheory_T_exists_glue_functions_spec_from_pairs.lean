-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_glue_functions_spec_from_pairs
-- name    : GlobalTheory.T.exists_glue_functions_spec_from_pairs
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:36:43.162431+00:00
-- url     : https://prove2.me/theorems/43b1fd6c-4928-44db-8b5a-ad23ad981a76
-- title:
--   T: exists glue functions spec from pairs
-- statement:
--   The T construction uses the exists glue functions spec from pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsGlueFunctionsSpecFromPairsStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsGlueFunctionsSpecFromPairsStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGlueFunctionsSpecFromPairs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SecPullA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGlueFunctionsSpecFromPairsStatement
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

theorem GlobalTheory.T.exists_glue_functions_spec_from_pairs : ∀ {X : Scheme.{0}} (B : Type) [CommRing B] (x : Sp B ⟶ X) (h : ∀ p : Pair x, Γ(Sp B, p.1.1.1)), (∀ p q : Pair x, ∀ hpq : p ≤ q, ((Sp B).presheaf.map (homOfLE (Pair.le_fst hpq)).op).hom (h q) = h p) → ∃ G : B, ∀ p : Pair x, (secMap (𝟙 (Sp B)) p.1.1.1).hom G = h p := by sorry
