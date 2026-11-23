-- Prove2me | Theorems.Thm_GlobalTheory_SelfDualLatticeCompare_hR_smul_right
-- name    : GlobalTheory.SelfDualLatticeCompare.hR_smul_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:45:38.428987+00:00
-- url     : https://prove2.me/theorems/860aa4e3-8290-4c1e-8014-dd8922988b32
-- title:
--   Self Dual Lattice Compare: h R smul right
-- statement:
--   The Self Dual Lattice Compare construction uses the h R smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DisjointSpanPerpLat.lean#L95-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DisjointSpanPerpLat.lean#L95-L98

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
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}
variable (R : Type) [CommRing R] [Algebra F R]

theorem GlobalTheory.SelfDualLatticeCompare.hR_smul_right {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y : Fin M → R ⊗[F] E)
    (c : R ⊗[F] E) : hR R σ J x (c • y) = c * hR R σ J x y := by sorry
