-- Prove2me | Theorems.Thm_GlobalTheory_SelfDualLatticeCompare_conclusion_iff
-- name    : GlobalTheory.SelfDualLatticeCompare.conclusion_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:53:05.019159+00:00
-- url     : https://prove2.me/theorems/30db424c-3d97-43cf-820c-d39ed56b88f0
-- title:
--   Self Dual Lattice Compare: conclusion iff
-- statement:
--   The Self Dual Lattice Compare construction uses the conclusion iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DisjointSpanPerpLat.lean#L177-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DisjointSpanPerpLat.lean#L177-L190

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_UnitaryLatticeOrthogonal
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_SelfDualLatticeActions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory GlobalTheory.SelfDualLatticeCompare
open GlobalTheory.IndefiniteRowSideFullHecke
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (v : HeightOneSpectrum (𝓞 F))

theorem GlobalTheory.SelfDualLatticeCompare.conclusion_iff (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    (L : Submodule (SelfDualLatticeActions.OEv E v) (SelfDualLatticeActions.Wv E v M)) :
    (UnitaryLatticeOrthogonal.HasONB σ J v L ∧
      (∀ L₁ : Submodule (UnitaryLatticeOrthogonal.OEv F E v) (Fin M → UnitaryLatticeOrthogonal.Ev F E v), UnitaryLatticeOrthogonal.IsSDLat σ J v L₁ →
        ∃ g : HA (Fv F v) σ J, ∀ y, y ∈ L ↔ UnitaryLatticeOrthogonal.act σ J v g y ∈ L₁) ∧
      ∀ β : (v.adicCompletionIntegers F)ˣ,
        UnitaryLatticeOrthogonal.UnitVectors σ J v L ((β : v.adicCompletionIntegers F) : Fv F v)) ↔
    (SelfDualLatticeActions.HasOrthonormalBasis v σ J L ∧
      (∀ L' : Submodule (SelfDualLatticeActions.OEv E v) (SelfDualLatticeActions.Wv E v M), SelfDualLatticeActions.IsSelfDualLat v σ J L' →
        ∃ g : HA (Fv F v) σ J, ∀ y, y ∈ L ↔ SelfDualLatticeActions.act v σ J g y ∈ L') ∧
      ∀ β : (v.adicCompletionIntegers F)ˣ,
        SelfDualLatticeActions.UnitVectorClaims v σ J L ((β : v.adicCompletionIntegers F) : Fv F v)) := by sorry
