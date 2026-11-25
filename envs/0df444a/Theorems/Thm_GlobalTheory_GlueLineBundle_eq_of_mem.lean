-- Prove2me | Theorems.Thm_GlobalTheory_GlueLineBundle_eq_of_mem
-- name    : GlobalTheory.GlueLineBundle.eq_of_mem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:14:05.44293+00:00
-- url     : https://prove2.me/theorems/014cac99-ea8f-5b21-9175-a12866b90817
-- title:
--   Glue Line Bundle: eq of mem
-- statement:
--   The Glue Line Bundle construction uses the eq of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/GlueLineBundles.lean#L108-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/GlueLineBundles.lean#L108-L110

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
variable {X : Scheme.{0}} {A : Type} (V : A → X.Opens) (M : ∀ a, LB (V a).toScheme)
variable {V M}

theorem GlobalTheory.GlueLineBundle.eq_of_mem (hdisj : ∀ a b x, x ∈ V a → x ∈ V b → a = b) {a b : A} (w : (V a).toScheme) {k : (M b).ι}
    (h : (V a).ι w ∈ NU V M ⟨b, k⟩) : a = b := by sorry
