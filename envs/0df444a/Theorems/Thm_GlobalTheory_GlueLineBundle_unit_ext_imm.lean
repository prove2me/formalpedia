-- Prove2me | Theorems.Thm_GlobalTheory_GlueLineBundle_unit_ext_imm
-- name    : GlobalTheory.GlueLineBundle.unit_ext_imm
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:08:46.360704+00:00
-- url     : https://prove2.me/theorems/2ab5fb79-058e-4e2d-b029-796fcf20245e
-- title:
--   Glue Line Bundle: unit ext imm
-- statement:
--   The Glue Line Bundle construction uses the unit ext imm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/GlueLineBundles.lean#L42-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/GlueLineBundles.lean#L42-L52

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
variable {X : Scheme.{0}}

theorem GlobalTheory.GlueLineBundle.unit_ext_imm {O : X.Opens} {a b : Γ(X, O)ˣ}
    (h : ∀ x ∈ O, ∃ (W : Scheme.{0}) (j : W ⟶ X) (_ : IsOpenImmersion j) (w : W), j w = x ∧
      gm j w O a = gm j w O b) : a = b := by sorry
