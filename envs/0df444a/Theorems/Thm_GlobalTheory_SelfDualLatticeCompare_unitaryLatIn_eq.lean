-- Prove2me | Theorems.Thm_GlobalTheory_SelfDualLatticeCompare_unitaryLatIn_eq
-- name    : GlobalTheory.SelfDualLatticeCompare.unitaryLatIn_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:22:43.465148+00:00
-- url     : https://prove2.me/theorems/250cbfd5-82e6-4b1c-a64e-8a334d2086b9
-- title:
--   Self Dual Lattice Compare: unitary Lat In eq
-- statement:
--   The Self Dual Lattice Compare construction uses the unitary Lat In eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DisjointSpanPerpLat.lean#L137-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DisjointSpanPerpLat.lean#L137-L139

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

theorem GlobalTheory.SelfDualLatticeCompare.unitaryLatIn_eq (P : Submodule (SelfDualLatticeActions.Ev E v) (SelfDualLatticeActions.Wv E v M))
    (L : Submodule (SelfDualLatticeActions.OEv E v) (SelfDualLatticeActions.Wv E v M)) :
    UnitaryLatticeOrthogonal.unitaryLatIn σ J v P L = SelfDualLatticeActions.latUnitaryIn v σ J P L := by sorry
