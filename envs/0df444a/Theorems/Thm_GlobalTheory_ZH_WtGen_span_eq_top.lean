-- Prove2me | Theorems.Thm_GlobalTheory_ZH_WtGen_span_eq_top
-- name    : GlobalTheory.ZH.WtGen.span_eq_top
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:08:12.481547+00:00
-- url     : https://prove2.me/theorems/d62554a1-36cb-54c4-8e47-fd3f1eb8d822
-- title:
--   Wt Gen: span eq top
-- statement:
--   The Wt Gen construction uses the span eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/PureSectionRatiosGenerateFunctions.lean#L109-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/PureSectionRatiosGenerateFunctions.lean#L109-L143

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueIsRatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsPartPartSec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GroupAlgebraSingleOneMemOfSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPowEqTorus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_PureSectionRatiosGenerateFunctions
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
noncomputable section
open GlobalTheory GlobalTheory.ZH GlobalTheory.ZH.WtGen
open GlobalTheory.ZH.WtPart
variable {k : Type} [Field k] (Φ : FibPre k)

theorem GlobalTheory.ZH.WtGen.span_eq_top [IsAlgClosed k] {α : Φ.E.X} {φ₀ : (Φ.H 1).Sec} (hφ₀ : Φ.Pure 0 φ₀)
    {V W : Φ.E.B.left.Opens} (hV : Φ.D.q.left ⁻¹ᵁ V ≤ Out.nonzeroLocus φ₀) (hW : IsAffineOpen W)
    (hWV : W ≤ V) (l : Φ.N₀.ι) (h : W ≤ Φ.N₀.U l)
    (hx : ∀ x : Φ.Pt, ∃ φ : (Φ.H 1).Sec, Φ.Pure α φ ∧ ⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus φ)
    (S : Subring Γ(Φ.G.left, Φ.D.q.left ⁻¹ᵁ W))
    (hS : ∀ (φ : (Φ.H 1).Sec) r, Φ.Pure α φ → IsRatio φ φ₀ (Φ.D.q.left ⁻¹ᵁ V) r →
      resG _ (Φ.D.q.left.preimage_mono hWV) r ∈ S) :
    Ideal.span {a : Γ(Φ.E.B.left, W) | (Φ.D.q.left.app W).hom a *
      mono Φ.D (Φ.ch l) W (h.trans (Φ.le l)) (Multiplicative.ofAdd α) ∈ S} = ⊤ := by sorry
