-- Prove2me | Theorems.Thm_GlobalTheory_GlueLineBundle_pgen_isoGen
-- name    : GlobalTheory.GlueLineBundle.pgen_isoGen
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:09:36.26921+00:00
-- url     : https://prove2.me/theorems/7889b36f-95c2-41b6-89a4-9b174c05d37b
-- title:
--   Glue Line Bundle: pgen iso Gen
-- statement:
--   The Glue Line Bundle construction uses the pgen iso Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/GlueLineBundles.lean#L179-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/GlueLineBundles.lean#L179-L194

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLineBundleExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_GlueLineBundles
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.GlueLineBundle
variable {X : Scheme.{0}} {A : Type} {V : A → X.Opens} {M : ∀ a, LB (V a).toScheme}

theorem GlobalTheory.GlueLineBundle.pgen_isoGen (hdisj : ∀ a b x, x ∈ V a → x ∈ V b → a = b) (hM : ∀ a, (M a).IsLB) (a : A) :
    PGen (isoGen (V := V) (M := M) a) := by sorry
