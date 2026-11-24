-- Prove2me | Theorems.Thm_GlobalTheory_SelfDualGenus_gram_inv_mem_semiLoc
-- name    : GlobalTheory.SelfDualGenus.gram_inv_mem_semiLoc
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:52:20.751918+00:00
-- url     : https://prove2.me/theorems/f7d5b5fa-2454-4b61-9f0e-a464876c411c
-- title:
--   Self Dual Genus: gram inv mem semi Loc
-- statement:
--   The Self Dual Genus construction uses the gram inv mem semi Loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/FiniteResidueFieldAdicCompletionIntegers.lean#L393-L446
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/FiniteResidueFieldAdicCompletionIntegers.lean#L393-L446

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing
open scoped Matrix TensorProduct nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LocalLattice
noncomputable section
open GlobalTheory GlobalTheory.SelfDualGenus
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
variable {G : Matrix (Fin r) (Fin r) E} {L : Submodule (𝓞 E) (Fin r → E)}
  {𝔟 : FractionalIdeal (𝓞 E)⁰ E} {g : GL (Fin r) E} {b : E}

theorem GlobalTheory.SelfDualGenus.gram_inv_mem_semiLoc (hd : G.det ≠ 0) (hL : L.FG)
    (hmod : ∀ x, x ∈ L ↔ ∀ y ∈ L, herm G x y ∈ 𝔟)
    (hg : ∀ x, (∃ s ∉ v.asIdeal, algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s • x ∈ L) ↔
      ∀ i, (((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ x) i ∈ semiLoc v) (hb0 : b ≠ 0)
    (hb : ∀ z, (∃ s ∉ v.asIdeal, (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s : E) * z ∈ 𝔟) ↔ b⁻¹ * z ∈ semiLoc v)
    (i j : Fin r) :
    b * ((g : Matrix (Fin r) (Fin r) E)ᵀ * G * (g : Matrix (Fin r) (Fin r) E).map cc)⁻¹ i j ∈
      semiLoc v := by sorry
