-- Prove2me | Theorems.Thm_GlobalTheory_Reg_TrivBound_comb_core
-- name    : GlobalTheory.Reg.TrivBound.comb_core
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:18:37.027717+00:00
-- url     : https://prove2.me/theorems/33bbc93e-b706-4c72-a2a2-562dab4226fd
-- title:
--   Triv Bound: comb core
-- statement:
--   The Triv Bound construction uses the comb core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/CombinedBoundAtTrivialValuationsOfCharts.lean#L263-L366
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/CombinedBoundAtTrivialValuationsOfCharts.lean#L263-L366

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegModelC
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_SCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegQFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FnTrdegOf
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RealPtGeo
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllProofFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_CombinedBoundAtTrivialValuationsOfCharts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Reg GlobalTheory.Reg.TrivBound
open IsLocalRing Formalism.L2.Pj GlobalTheory.Reg

theorem GlobalTheory.Reg.TrivBound.comb_core {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CharZero O]
    [CommRing A] [IsDomain A] [Algebra O A] [Algebra.FiniteType O A] [Module.Flat O A]
    [IsIntegrallyClosed A] (ϖ : O) (eO : ℕ) (heO : 0 < eO)
    (fw fe : FractionRing A) (hfw0 : fw ≠ 0) (x : A) (hx : x ≠ 0)
    (ye : A) (hye : ye ≠ 0) (te : ℕ)
    (hfe : fe * algebraMap A (FractionRing A) ((algebraMap O A ϖ * x) ^ te) = algebraMap A (FractionRing A) ye)
    (yw : A) (tw : ℕ)
    (hfw : fw⁻¹ * algebraMap A (FractionRing A) ((algebraMap O A ϖ * x) ^ tw) = algebraMap A (FractionRing A) yw)
    (nu0 c' : ℝ) (N : ℕ) (Aexp : ℤ) (B : ℕ) (hA : (eO : ℝ) * N * nu0 ≤ Aexp) (hB : (N : ℝ) * c' ≤ B)
    (halg : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra O V]
      [Module.Finite O V] (φ : A →ₐ[O] V), φ x ≠ 0 → ∃ (e : ℕ) (W T : EReal), 0 < e ∧
        vV (K' := FractionRing V) V (algebraMap V (FractionRing V) (algebraMap O V ϖ)) * (eO : ℤ) = e ∧
        ChV φ.toRingHom e fw W ∧ ChV φ.toRingHom e fe T ∧ 0 ≤ T ∧
        (T ≠ ⊤ → W ≤ (nu0 : EReal) + (c' : EReal) * T))
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra O V] (φ : A →ₐ[O] V)
    (hφx : φ x ≠ 0) (hφϖ : algebraMap O V ϖ ≠ 0)
    (hqq : (maximalIdeal V).comap φ.toRingHom ⊔ Ideal.map (algebraMap O A) (maximalIdeal O) ≠ ⊤)
    (e : ℕ) (w t : ℝ) (hW : ChV φ.toRingHom e fw (w : EReal)) (hT : ChV φ.toRingHom e fe (t : EReal)) :
    (N : ℝ) * w ≤ Aexp * vr e (algebraMap O V ϖ) + B * t := by sorry
