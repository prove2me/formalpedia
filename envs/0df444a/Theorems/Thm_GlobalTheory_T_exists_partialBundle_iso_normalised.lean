-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_partialBundle_iso_normalised
-- name    : GlobalTheory.T.exists_partialBundle_iso_normalised
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:37:56.985932+00:00
-- url     : https://prove2.me/theorems/25e8c5a0-c557-402b-ae3b-eaa79cb63531
-- title:
--   T: exists partial Bundle iso normalised
-- statement:
--   The T construction uses the exists partial Bundle iso normalised property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsPartialBundleIsoNormalisedStatement.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsPartialBundleIsoNormalisedStatement.lean#L12-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsPartialBundleIsoNormalised
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsPartialBundleIsoNormalisedStatement
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
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_partialBundle_iso_normalised : ∀ (X S : Scheme.{0}) (p : X ⟶ S) (e : S ⟶ X) (V V' : S.Opens) (M M' : LB X) (r : (M.pull e).Gen) (r' : (M'.pull e).Gen), e ≫ p = 𝟙 S → ⨆ a, M.U a = p ⁻¹ᵁ V → ⨆ a, M'.U a = p ⁻¹ᵁ V' → r.IsGen → r'.IsGen → LBIso M' M → ∃ w : LB.Iso M' M, w.IsGen ∧ ∀ (x : S) (a : M.ι) (b : M'.ι), e x ∈ M.U a → e x ∈ M'.U b → gm (𝟙 S) x ((M.pull e).U fun _ => a) (r.s fun _ => a) = gm e x (M.U a ⊓ M'.U b) (w.s (a, b)) * gm (𝟙 S) x ((M'.pull e).U fun _ => b) (r'.s fun _ => b) := by sorry
