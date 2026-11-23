-- Prove2me | Theorems.Thm_GlobalTheory_SelfDualLatticeCompare_sigR_sigR
-- name    : GlobalTheory.SelfDualLatticeCompare.sigR_sigR
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:59:16.170422+00:00
-- url     : https://prove2.me/theorems/41aa9494-2140-4df3-a82e-d983c9bed9ba
-- title:
--   Self Dual Lattice Compare: sig R sig R
-- statement:
--   The Self Dual Lattice Compare construction uses the sig R sig R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DisjointSpanPerpLat.lean#L70-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DisjointSpanPerpLat.lean#L70-L76

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

theorem GlobalTheory.SelfDualLatticeCompare.sigR_sigR (h : IsCMExt F E σ) (z : R ⊗[F] E) : sigR R σ (sigR R σ z) = z := by sorry
