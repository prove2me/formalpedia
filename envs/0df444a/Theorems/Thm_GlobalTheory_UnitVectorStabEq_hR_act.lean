-- Prove2me | Theorems.Thm_GlobalTheory_UnitVectorStabEq_hR_act
-- name    : GlobalTheory.UnitVectorStabEq.hR_act
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:39:23.486805+00:00
-- url     : https://prove2.me/theorems/d97d8538-e2ae-4422-8f2f-bfe01a9204be
-- title:
--   Unit Vector Stab Eq: h R act
-- statement:
--   The Unit Vector Stab Eq construction uses the h R act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/StabLatInfStabVec.lean#L51-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/StabLatInfStabVec.lean#L51-L56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_StabLatInfStabVec
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
open GlobalTheory GlobalTheory.UnitVectorStabEq
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (v : HeightOneSpectrum (𝓞 F))

theorem GlobalTheory.UnitVectorStabEq.hR_act (g : HA (Fv F v) σ J) (y z : Fin M → Ev F E v) :
    hR (Fv F v) σ J (act σ J v g y) (act σ J v g z) = hR (Fv F v) σ J y z := by sorry
