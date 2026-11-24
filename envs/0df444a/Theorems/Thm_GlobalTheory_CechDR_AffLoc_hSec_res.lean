-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_AffLoc_hSec_res
-- name    : GlobalTheory.CechDR.AffLoc.hSec_res
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:59:38.983817+00:00
-- url     : https://prove2.me/theorems/247c3de3-c642-4b47-8fa6-2b58e12fbc38
-- title:
--   Aff Loc: h Sec res
-- statement:
--   The Aff Loc construction uses the h Sec res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CocycleLocalSectionsRestrictCompatibly.lean#L34-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CocycleLocalSectionsRestrictCompatibly.lean#L34-L55

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

theorem GlobalTheory.CechDR.AffLoc.hSec_res (f : Z1 ((IsTriv s).ι ⋙ O (dp0 R) s)) (g : C0 (OAff s))
    (hg : ∀ ⦃U V : AffOp X⦄ (a : U ⟶ V), g V - Sec.res s (leOfHom a.unop) (g U) = fv f ((affF s).map a))
    (T : TT s) (p q : Pair (pt T)) (hpq : p ≤ q) :
    Sec.res (algStr R T.obj.B) (Pair.le_fst hpq) (hSec f g T q) = hSec f g T p := by sorry
