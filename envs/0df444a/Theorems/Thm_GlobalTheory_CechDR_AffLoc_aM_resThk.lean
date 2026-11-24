-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_AffLoc_aM_resThk
-- name    : GlobalTheory.CechDR.AffLoc.aM_resThk
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:59:11.275792+00:00
-- url     : https://prove2.me/theorems/314a1cf2-f47d-4765-9f32-bf78a5aee0f4
-- title:
--   Aff Loc: a M res Thk
-- statement:
--   The Aff Loc construction uses the a M res Thk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CocycleLocalSectionsRestrictCompatibly.lean#L28-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CocycleLocalSectionsRestrictCompatibly.lean#L28-L32

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

theorem GlobalTheory.CechDR.AffLoc.aM_resThk (T : TT s) {p q : Pair (pt T)} (hpq : p ≤ q) :
    aM T q ≫ resThk T hpq = (affF s).map (homOfLE (Pair.le_snd hpq)).op ≫ aM T p := by sorry
