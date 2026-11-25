-- Prove2me | Theorems.Thm_GlobalTheory_SelfDualLatticeCompare_sL_eq
-- name    : GlobalTheory.SelfDualLatticeCompare.sL_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:23:35.345927+00:00
-- url     : https://prove2.me/theorems/c3b7da25-5b76-4eda-8106-643b6a71c2e7
-- title:
--   Self Dual Lattice Compare: s L eq
-- statement:
--   The Self Dual Lattice Compare construction uses the s L eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DisjointSpanPerpLat.lean#L143-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DisjointSpanPerpLat.lean#L143-L144

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

theorem GlobalTheory.SelfDualLatticeCompare.sL_eq (L : Submodule (SelfDualLatticeActions.OEv E v) (SelfDualLatticeActions.Wv E v M)) (β : Fv F v) :
    UnitaryLatticeOrthogonal.SL σ J v L β = SelfDualLatticeActions.sphere v σ J L β := by sorry
