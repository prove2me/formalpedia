-- Prove2me | Theorems.Thm_GlobalTheory_UnramSelfDual_exists_frame
-- name    : GlobalTheory.UnramSelfDual.exists_frame
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:47:10.084104+00:00
-- url     : https://prove2.me/theorems/4b016ec5-d866-48c9-9960-51f90dd7a1b8
-- title:
--   Unram Self Dual: exists frame
-- statement:
--   The Unram Self Dual construction uses the exists frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsOfFixedInt.lean#L448-L464
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsOfFixedInt.lean#L448-L464

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
import Theorems.Thm_GlobalTheory_SelfDualGenus_exists_frame

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
variable {M : ℕ} {J : Matrix (Fin M) (Fin M) E}

theorem GlobalTheory.UnramSelfDual.exists_frame (h : IsCMExt F E σ) (hv : UnramAt F E v) {m : ℕ}
    {J : Matrix (Fin (m + 1)) (Fin (m + 1)) E} (hJ : IsHermND σ J)
    {L : Submodule (OEv F E v) (Fin (m + 1) → Ev F E v)} (hL : IsSDLat σ J v L) :
    (∃ x ∈ L, hR (Fv F v) σ J x x = 1) ∧ ∀ x ∈ L, hR (Fv F v) σ J x x = 1 →
      ∃ e : Fin (m + 1) → Fin (m + 1) → Ev F E v, (∀ i, e i ∈ L) ∧
        (∀ i j, hform (sigR (Fv F v) σ) (JR (Fv F v) J) (e i) (e j) = if i = j then 1 else 0) ∧
        e 0 = x := by sorry
