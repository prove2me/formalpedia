-- Prove2me | Theorems.Thm_GlobalTheory_KS_Square_exists_compare
-- name    : GlobalTheory.KS.Square.exists_compare
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:57:48.526259+00:00
-- url     : https://prove2.me/theorems/9660efd7-8a77-474c-9d04-c2a10c592c32
-- title:
--   Square: exists compare
-- statement:
--   The Square construction uses the exists compare property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsIsSymmOfSquare.lean#L125-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsIsSymmOfSquare.lean#L125-L149

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsCobOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_KunnethSymmProductAffineCoversStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsSymmOfSquare
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.Square
variable {Z : Scheme.{0}}
variable {J : Type} {V : J → Z.Opens}

theorem GlobalTheory.KS.Square.exists_compare (hV : ⨆ α, V α = ⊤) {Y : Scheme.{0}} (p : Z ⟶ Y) {T : Y.Opens}
    {W A B E : Z.Opens} (hA : W ≤ A) (hB : W ≤ B) (hE : W ≤ E) (hT : W ≤ p ⁻¹ᵁ T) {g : ℕ}
    (θ : Fin g → Γ(Y, T)) (e : Fin g → ∀ α, Γ(Z, E ⊓ V α))
    (k : C1 fun α => A ⊓ V α) (k' : C1 fun α => B ⊓ V α)
    (c : ∀ α, Γ(Z, A ⊓ V α)) (c' : ∀ α, Γ(Z, B ⊓ V α))
    (hc : ∀ α β O, O ≤ A ⊓ V α ⊓ V β → rsT (k α β) O = rsT (c β) O - rsT (c α) O)
    (hc' : ∀ α β O, O ≤ B ⊓ V α ⊓ V β → rsT (k' α β) O = rsT (c' β) O - rsT (c' α) O)
    (h : ∀ α β O, O ≤ W ⊓ V α ⊓ V β → rsT (k' α β) O - rsT (k α β) O =
      ∑ a, pbT p (θ a) O * (rsT (e a α) O - rsT (e a β) O)) :
    ∃ s : Γ(Z, W), ∀ α O, O ≤ W ⊓ V α →
      rsT s O = rsT (c' α) O - rsT (c α) O + ∑ a, pbT p (θ a) O * rsT (e a α) O := by sorry
