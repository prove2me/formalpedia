-- Prove2me | Theorems.Thm_GlobalTheory_BundleNormalise_exists_iso_normalised
-- name    : GlobalTheory.BundleNormalise.exists_iso_normalised
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:04:34.851575+00:00
-- url     : https://prove2.me/theorems/c34cb1b2-ac7f-45f5-8feb-2eb822f58cb4
-- title:
--   Bundle Normalise: exists iso normalised
-- statement:
--   The Bundle Normalise construction uses the exists iso normalised property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsPartialBundleIsoNormalised.lean#L79-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsPartialBundleIsoNormalised.lean#L79-L179

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsGenOfRigid
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsPartialBundleIsoNormalised
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
noncomputable section
open GlobalTheory GlobalTheory.BundleNormalise
open GlobalTheory.RigidTriv
variable {X Y : Scheme.{0}}

theorem GlobalTheory.BundleNormalise.exists_iso_normalised : ∀ (X S : Scheme.{0}) (p : X ⟶ S) (e : S ⟶ X) (V V' : S.Opens) (M M' : LB X) (r : (M.pull e).Gen) (r' : (M'.pull e).Gen), e ≫ p = 𝟙 S → ⨆ a, M.U a = p ⁻¹ᵁ V → ⨆ a, M'.U a = p ⁻¹ᵁ V' → r.IsGen → r'.IsGen → LBIso M' M → ∃ w : LB.Iso M' M, w.IsGen ∧ ∀ (x : S) (a : M.ι) (b : M'.ι), e x ∈ M.U a → e x ∈ M'.U b → gm (𝟙 S) x ((M.pull e).U fun _ => a) (r.s fun _ => a) = gm e x (M.U a ⊓ M'.U b) (w.s (a, b)) * gm (𝟙 S) x ((M'.pull e).U fun _ => b) (r'.s fun _ => b) := by sorry
