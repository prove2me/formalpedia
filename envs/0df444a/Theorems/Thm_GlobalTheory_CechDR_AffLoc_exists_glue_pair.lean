-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_AffLoc_exists_glue_pair
-- name    : GlobalTheory.CechDR.AffLoc.exists_glue_pair
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:59:12.515273+00:00
-- url     : https://prove2.me/theorems/4da74849-ebdd-4e26-ba0d-8309190ea1a5
-- title:
--   Aff Loc: exists glue pair
-- statement:
--   The Aff Loc construction uses the exists glue pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsGlueFunctionsSpecFromPairs.lean#L11-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsGlueFunctionsSpecFromPairs.lean#L11-L54

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SecPullA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGlueFunctionsSpecFromPairs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechDR.AffLoc
open GlobalTheory GlobalTheory.CechDR GlobalTheory.CechDR.AffLoc

theorem GlobalTheory.CechDR.AffLoc.exists_glue_pair {X : Scheme.{0}} (B : Type) [CommRing B] (x : Sp B ⟶ X)
    (h : ∀ p : Pair x, Γ(Sp B, p.1.1.1))
    (hh : ∀ p q : Pair x, ∀ hpq : p ≤ q,
      ((Sp B).presheaf.map (homOfLE (Pair.le_fst hpq)).op).hom (h q) = h p) :
    ∃ G : B, ∀ p : Pair x, (secMap (𝟙 (Sp B)) p.1.1.1).hom G = h p := by sorry
