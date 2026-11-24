-- Prove2me | Theorems.Thm_GlobalTheory_SelfDualGenus_locEmb_mem_locLattice_iff
-- name    : GlobalTheory.SelfDualGenus.locEmb_mem_locLattice_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:52:27.615947+00:00
-- url     : https://prove2.me/theorems/933e031c-d698-42c8-b15a-8790643863e4
-- title:
--   Self Dual Genus: loc Emb mem loc Lattice iff
-- statement:
--   The Self Dual Genus construction uses the loc Emb mem loc Lattice iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/FiniteResidueFieldAdicCompletionIntegers.lean#L516-L523
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/FiniteResidueFieldAdicCompletionIntegers.lean#L516-L523

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
variable {L : Submodule (𝓞 E) (Fin r → E)}

theorem GlobalTheory.SelfDualGenus.locEmb_mem_locLattice_iff (hL : ReciprocityTheory.MultiplicativeHeights.IsLattice L) (x : Fin r → E) :
    (fun i => locEmb v (x i)) ∈ locLattice v L ↔
      ∃ s ∉ v.asIdeal, algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s • x ∈ L := by sorry
