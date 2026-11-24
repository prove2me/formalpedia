-- Prove2me | Theorems.Thm_GlobalTheory_UnramSelfDual_exists_uniformiser
-- name    : GlobalTheory.UnramSelfDual.exists_uniformiser
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:46:47.403739+00:00
-- url     : https://prove2.me/theorems/ce475146-f9c1-4df8-b9b0-d2842a85b39b
-- title:
--   Unram Self Dual: exists uniformiser
-- statement:
--   The Unram Self Dual construction uses the exists uniformiser property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsOfFixedInt.lean#L390-L411
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsOfFixedInt.lean#L390-L411

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

theorem GlobalTheory.UnramSelfDual.exists_uniformiser (h : IsCMExt F E σ) :
    ∃ p q : Ev F E v, p ∈ OEv F E v ∧ sigR (Fv F v) σ p = p ∧ p * q = 1 ∧ q ∉ OEv F E v ∧
      ∀ a ∈ OEv F E v, sigR (Fv F v) σ a = a →
        (∃ b ∈ OEv F E v, a * b = 1) ∨ ∃ b ∈ OEv F E v, a = p * b := by sorry
