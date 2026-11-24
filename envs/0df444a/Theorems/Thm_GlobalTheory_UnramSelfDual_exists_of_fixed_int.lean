-- Prove2me | Theorems.Thm_GlobalTheory_UnramSelfDual_exists_of_fixed_int
-- name    : GlobalTheory.UnramSelfDual.exists_of_fixed_int
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T13:40:23.91156+00:00
-- url     : https://prove2.me/theorems/06e27e7c-aff7-4826-a6fd-d271d2ab3725
-- title:
--   Unram Self Dual: exists of fixed int
-- statement:
--   The Unram Self Dual construction uses the exists of fixed int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsOfFixedInt.lean#L380-L388
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsOfFixedInt.lean#L380-L388

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsSubConjNotMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsReflection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SelfDualLatticeProjectionMemOfUnitLength
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_StabLatInfStabVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RestrHomSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsOfFixedInt
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
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal Formalism.UG
open GlobalTheory GlobalTheory.UnramSelfDual
open GlobalTheory.SelfDualLatticeCompare IsLocalRing
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} (v : HeightOneSpectrum (𝓞 F))

theorem GlobalTheory.UnramSelfDual.exists_of_fixed_int (h : IsCMExt F E σ) {a : Ev F E v} (hO : a ∈ OEv F E v)
    (ha : sigR (Fv F v) σ a = a) :
    ∃ r : v.adicCompletionIntegers F, algebraMap _ (Ev F E v) r = a := by sorry
