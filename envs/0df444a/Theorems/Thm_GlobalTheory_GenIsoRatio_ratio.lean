-- Prove2me | Theorems.Thm_GlobalTheory_GenIsoRatio_ratio
-- name    : GlobalTheory.GenIsoRatio.ratio
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:58:23.154183+00:00
-- url     : https://prove2.me/theorems/bace8e0a-d7e7-5f7c-be76-813e7588810c
-- title:
--   Gen Iso Ratio: ratio
-- statement:
--   The Gen Iso Ratio construction uses the ratio property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsGlobalUnitRatioGenericLineBundleIsos.lean#L25-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsGlobalUnitRatioGenericLineBundleIsos.lean#L25-L74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_RigidifiedPartialLineBundleIsoCocycle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGlobalUnitRatioGenericLineBundleIsos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.GenIsoRatio

theorem GlobalTheory.GenIsoRatio.ratio : ∀ (X Y : Scheme.{0}) (β : Y ⟶ X) (P M : LB X) (N : LB Y), P.IsLB → M.IsLB → N.IsLB → ∀ (w : LB.Iso (M.pull β) N) (w₁ : LB.Iso (P.pull β) N) (v : LB.Iso P M), w.IsGen → w₁.IsGen → v.IsGen → ∃ u : Γ(Y, ⊤)ˣ, ∀ (n : N.ι) (i : P.ι) (m : M.ι) (hle : N.U n ⊓ (P.pull β).U (fun _ => i) ⊓ (M.pull β).U (fun _ => m) ≤ β ⁻¹ᵁ (M.U m ⊓ P.U i)), GlobalTheory.AbLaw.rs _ (inf_le_left : N.U n ⊓ (P.pull β).U (fun _ => i) ⊓ (M.pull β).U (fun _ => m) ≤ N.U n ⊓ (P.pull β).U (fun _ => i)) (w₁.s (n, fun _ => i)).val = GlobalTheory.AbLaw.rs _ (le_top : N.U n ⊓ (P.pull β).U (fun _ => i) ⊓ (M.pull β).U (fun _ => m) ≤ ⊤) (u : Γ(Y, ⊤)) * (β.appLE (M.U m ⊓ P.U i) _ hle).hom (v.s (m, i)).val * GlobalTheory.AbLaw.rs _ (le_inf (inf_le_left.trans inf_le_left) inf_le_right : N.U n ⊓ (P.pull β).U (fun _ => i) ⊓ (M.pull β).U (fun _ => m) ≤ N.U n ⊓ (M.pull β).U (fun _ => m)) (w.s (n, fun _ => m)).val := by sorry
