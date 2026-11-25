-- Prove2me | Theorems.Thm_GlobalTheory_SelfDualLatticeCompare_stabLat_eq
-- name    : GlobalTheory.SelfDualLatticeCompare.stabLat_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:27:12.585333+00:00
-- url     : https://prove2.me/theorems/33b2af93-e4b3-51e1-abcc-14091784d43a
-- title:
--   Self Dual Lattice Compare: stab Lat eq
-- statement:
--   The Self Dual Lattice Compare construction uses the stab Lat eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DisjointSpanPerpLat.lean#L131-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DisjointSpanPerpLat.lean#L131-L132

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

theorem GlobalTheory.SelfDualLatticeCompare.stabLat_eq (L : Submodule (SelfDualLatticeActions.OEv E v) (SelfDualLatticeActions.Wv E v M)) :
    UnitaryLatticeOrthogonal.stabLat σ J v L = SelfDualLatticeActions.latStab v σ J L := by sorry
