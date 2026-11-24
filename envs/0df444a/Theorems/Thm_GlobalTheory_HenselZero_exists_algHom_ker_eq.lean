-- Prove2me | Theorems.Thm_GlobalTheory_HenselZero_exists_algHom_ker_eq
-- name    : GlobalTheory.HenselZero.exists_algHom_ker_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T14:19:14.652797+00:00
-- url     : https://prove2.me/theorems/06ffc084-5397-469b-9c98-21ef8527cd5f
-- title:
--   Hensel Zero: exists alg Hom ker eq
-- statement:
--   The Hensel Zero construction uses the exists alg Hom ker eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/FormallySmoothQuotient.lean#L51-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/FormallySmoothQuotient.lean#L51-L103

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsResEqOfUnitInChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_FormallySmoothQuotient
import Theorems.Thm_GlobalTheory_SqZero_UnitInChart_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HenselZero
open IsLocalRing GlobalTheory.SqZero

theorem GlobalTheory.HenselZero.exists_algHom_ker_eq {O S ι : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CommRing S] [IsLocalRing S] [IsNoetherianRing S] [Algebra O S]
    [Algebra.FormallySmooth O S] [Fintype ι] [DecidableEq ι] (f : ι → S) (u : S →+* ResidueField O)
    (hu : ∀ r, u (algebraMap O S r) = residue O r) (hf : ∀ i, u (f i) = 0)
    (χ : ι → (S →+* DualNumber (ResidueField O))) (h₁ : ∀ k a, (χ k a).fst = u a)
    (h₂ : ∀ k r, χ k (algebraMap O S r) = algebraMap (ResidueField O) _ (residue O r))
    (hd : (Matrix.of fun i k => (χ k (f i)).snd).det ≠ 0)
    (hm : maximalIdeal S ≤ Ideal.span (Set.range f) ⊔ (maximalIdeal O).map (algebraMap O S)) :
    ∃ ψ : S →ₐ[O] O, (∀ a, residue O (ψ a) = u a) ∧ RingHom.ker ψ = Ideal.span (Set.range f) := by sorry
