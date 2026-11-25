-- Prove2me | Theorems.Thm_GlobalTheory_InvFieldRing_res_constFn
-- name    : GlobalTheory.InvFieldRing.res_constFn
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:11:47.860258+00:00
-- url     : https://prove2.me/theorems/78f7324f-f02e-4f52-8074-f099f79a92ad
-- title:
--   Inv Field Ring: res const Fn
-- statement:
--   The Inv Field Ring construction uses the res const Fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SurjectiveSpMapFst.lean#L119-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SurjectiveSpMapFst.lean#L119-L122

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__DenseInterior_23def473f6482931
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DualNumberSectionsUniqueDecomposition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SurjectiveSpMapFst
import Theorems.Thm_GlobalTheory_RelConstThickening_res_constFn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj
noncomputable section
open GlobalTheory GlobalTheory.InvFieldRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.InvFieldRing.res_constFn {R : Type} [CommRing R] {Y : Scheme.{0}} (f : Y ⟶ Sp R) {V W : Y.Opens} (h : W ≤ V) (a : R) :
    resG Y h (constFn f V a) = constFn f W a := by sorry
