-- Prove2me | Theorems.Thm_GlobalTheory_SelfDualLatticeSplit_proj_apply
-- name    : GlobalTheory.SelfDualLatticeSplit.proj_apply
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:22:55.207459+00:00
-- url     : https://prove2.me/theorems/8d2531da-e92a-4d02-b4e8-a60c79d20943
-- title:
--   Self Dual Lattice Split: proj apply
-- statement:
--   The Self Dual Lattice Split construction uses the proj apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SelfDualLatticeProjectionMemOfUnitLength.lean#L33-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SelfDualLatticeProjectionMemOfUnitLength.lean#L33-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SelfDualLatticeProjectionMemOfUnitLength
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal
open GlobalTheory GlobalTheory.SelfDualLatticeSplit
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (v : HeightOneSpectrum (𝓞 F))

theorem GlobalTheory.SelfDualLatticeSplit.proj_apply (x : Fin M → Ev F E v) (b : Ev F E v) (y : Fin M → Ev F E v) :
    proj σ J v x b y = y - (b * hR (Fv F v) σ J x y) • x := by sorry
