-- Prove2me | Theorems.Thm_GlobalTheory_Published_CohDimTwoGlobal_of_nsmul
-- name    : GlobalTheory.Published.CohDimTwoGlobal.of_nsmul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:21:07.435907+00:00
-- url     : https://prove2.me/theorems/5b4e04e4-9279-5b23-b4b4-99f4b4387edb
-- title:
--   Coh Dim Two Global: of nsmul
-- statement:
--   The Coh Dim Two Global construction uses the of nsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/CohDimTwoLocalOfLocalFiniteness.lean#L88-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/CohDimTwoLocalOfLocalFiniteness.lean#L88-L95

import Mathlib
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__CohDimTwoLocalOfLocalFiniteness_b2c2e165733ad400
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation ReciprocityTheory.Gal Formalism.ConjugateSelfDual
open GlobalTheory GlobalTheory.Published
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  (l : ℕ) [Fact l.Prime] {R : Type*} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [Finite M] [TopologicalSpace M] [DiscreteTopology M]

theorem GlobalTheory.Published.CohDimTwoGlobal.of_nsmul (h : CohDimTwoGlobal) [IsTotallyComplex F] (r : ℕ)
    (hM : ∀ m : M, (l ^ r) • m = 0) {S : Finset (HeightOneSpectrum (𝓞 F))}
    (rhoS : Representation R (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
    (hS : ContainsAbove S l) (hc : ContAction rhoS) (n : ℕ) (hn : 3 ≤ n) :
    Subsingleton (Hn rhoS n) := by sorry
