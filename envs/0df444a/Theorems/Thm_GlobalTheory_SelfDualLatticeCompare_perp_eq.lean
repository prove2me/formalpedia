-- Prove2me | Theorems.Thm_GlobalTheory_SelfDualLatticeCompare_perp_eq
-- name    : GlobalTheory.SelfDualLatticeCompare.perp_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:26:47.072846+00:00
-- url     : https://prove2.me/theorems/639ced88-62ec-50b7-8653-554051632b11
-- title:
--   Self Dual Lattice Compare: perp eq
-- statement:
--   The Self Dual Lattice Compare construction uses the perp eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DisjointSpanPerpLat.lean#L119-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DisjointSpanPerpLat.lean#L119-L119

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

theorem GlobalTheory.SelfDualLatticeCompare.perp_eq : UnitaryLatticeOrthogonal.perp σ J v = SelfDualLatticeActions.perp v σ J := by sorry
