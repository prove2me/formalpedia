-- Prove2me | Theorems.Thm_GlobalTheory_KS_Square_exists_split
-- name    : GlobalTheory.KS.Square.exists_split
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:58:22.375199+00:00
-- url     : https://prove2.me/theorems/6c27e321-5a20-4ebe-a9ad-4a1e0c3a31e8
-- title:
--   Square: exists split
-- statement:
--   The Square construction uses the exists split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsIsSymmOfSquare.lean#L112-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsIsSymmOfSquare.lean#L112-L123

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

theorem GlobalTheory.KS.Square.exists_split (hV : ⨆ α, V α = ⊤) {W : Z.Opens} (hW : IsAffineOpen W)
    (k : C1 fun α => W ⊓ V α) (hk : IsCoc _ k) :
    ∃ c : ∀ α, Γ(Z, W ⊓ V α), ∀ α β O, O ≤ W ⊓ V α ⊓ V β →
      rsT (k α β) O = rsT (c β) O - rsT (c α) O := by sorry
