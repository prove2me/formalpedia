-- Prove2me | Theorems.Thm_GlobalTheory_SelfDualLatticeCompare_disjoint_span_perpLat
-- name    : GlobalTheory.SelfDualLatticeCompare.disjoint_span_perpLat
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:53:15.749188+00:00
-- url     : https://prove2.me/theorems/d8e2ff41-9787-4401-ad41-9543dd6e4360
-- title:
--   Self Dual Lattice Compare: disjoint span perp Lat
-- statement:
--   The Self Dual Lattice Compare construction uses the disjoint span perp Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DisjointSpanPerpLat.lean#L154-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DisjointSpanPerpLat.lean#L154-L164

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

theorem GlobalTheory.SelfDualLatticeCompare.disjoint_span_perpLat (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    (L : Submodule (SelfDualLatticeActions.OEv E v) (SelfDualLatticeActions.Wv E v M)) (x : SelfDualLatticeActions.Wv E v M)
    (hx : IsUnit (qR (Fv F v) σ J x)) :
    Disjoint (Submodule.span (SelfDualLatticeActions.OEv E v) {x}) (SelfDualLatticeActions.perpLat v σ J x L) := by sorry
