-- Prove2me | Theorems.Thm_GlobalTheory_ThetaQuotient_exists_glue_of_values
-- name    : GlobalTheory.ThetaQuotient.exists_glue_of_values
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:06:13.564809+00:00
-- url     : https://prove2.me/theorems/5882bea5-17db-4e9e-9be6-9f7e4bccaa74
-- title:
--   Theta Quotient: exists glue of values
-- statement:
--   The Theta Quotient construction uses the exists glue of values property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/EvalDivOfIsHomogeneous.lean#L41-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/EvalDivOfIsHomogeneous.lean#L41-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_EvalDivOfIsHomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.ThetaQuotient

theorem GlobalTheory.ThetaQuotient.exists_glue_of_values {X : Over (Sp ℂ)}
    (hext : ∀ (U : X.left.Opens) (f f' : Γ(X.left, U)),
      (∀ x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U → valAt' x.left U f = valAt' x.left U f') → f = f')
    {κ : Type} (V : κ → X.left.Opens) (s : ∀ i, Γ(X.left, V i)) (a : (𝟙_ (Over (Sp ℂ)) ⟶ X) → ℂ)
    (hs : ∀ i x, ⊤ ≤ x.left ⁻¹ᵁ V i → valAt' x.left (V i) (s i) = a x) :
    ∃ φ : Γ(X.left, ⨆ i, V i), ∀ x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ x.left ⁻¹ᵁ (⨆ i, V i) →
      valAt' x.left (⨆ i, V i) φ = a x := by sorry
