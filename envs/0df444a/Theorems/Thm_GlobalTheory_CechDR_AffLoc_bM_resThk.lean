-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_AffLoc_bM_resThk
-- name    : GlobalTheory.CechDR.AffLoc.bM_resThk
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:59:28.078543+00:00
-- url     : https://prove2.me/theorems/0585a63f-fbe8-4f03-8fbc-5c4af763054c
-- title:
--   Aff Loc: b M res Thk
-- statement:
--   The Aff Loc construction uses the b M res Thk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CocycleLocalSectionsRestrictCompatibly.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CocycleLocalSectionsRestrictCompatibly.lean#L24-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SecPullA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CocycleLocalSectionsRestrictCompatibly
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
open CategoryTheory AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh
  GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechDR.AffLoc
open GlobalTheory GlobalTheory.CechDR GlobalTheory.CechDR.AffLoc
variable {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R}

theorem GlobalTheory.CechDR.AffLoc.bM_resThk (T : TT s) {p q : Pair (pt T)} (hpq : p ≤ q) :
    bM T q ≫ resThk T hpq = bM T p := by sorry
