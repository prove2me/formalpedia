-- Prove2me | Theorems.Thm_GlobalTheory_SelfDualLatticeSplit_mem_perp
-- name    : GlobalTheory.SelfDualLatticeSplit.mem_perp
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:22:47.432843+00:00
-- url     : https://prove2.me/theorems/ac4ea715-b738-4eaa-ad4e-068d0361d32f
-- title:
--   Self Dual Lattice Split: mem perp
-- statement:
--   The Self Dual Lattice Split construction uses the mem perp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SelfDualLatticeProjectionMemOfUnitLength.lean#L36-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SelfDualLatticeProjectionMemOfUnitLength.lean#L36-L37

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

theorem GlobalTheory.SelfDualLatticeSplit.mem_perp (x y : Fin M → Ev F E v) : y ∈ perp σ J v x ↔ hR (Fv F v) σ J x y = 0 := by sorry
