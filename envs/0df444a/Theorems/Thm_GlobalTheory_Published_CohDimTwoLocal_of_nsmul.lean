-- Prove2me | Theorems.Thm_GlobalTheory_Published_CohDimTwoLocal_of_nsmul
-- name    : GlobalTheory.Published.CohDimTwoLocal.of_nsmul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:16:22.90194+00:00
-- url     : https://prove2.me/theorems/44acb215-a7b4-4a5a-b843-4c2d3bac4910
-- title:
--   Coh Dim Two Local: of nsmul
-- statement:
--   The Coh Dim Two Local construction uses the of nsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/CohDimTwoLocalOfLocalFiniteness.lean#L97-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/CohDimTwoLocalOfLocalFiniteness.lean#L97-L104

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

theorem GlobalTheory.Published.CohDimTwoLocal.of_nsmul (h : CohDimTwoLocal) (r : ℕ)
    (hM : ∀ m : M, (l ^ r) • m = 0) {v : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω}
    (rho : Representation R (Dec (F := F) A) M)
    (hA : IsPlaceOver A v) (hc : ContAction rho) (n : ℕ) (hn : 3 ≤ n) :
    Subsingleton (Hn rho n) := by sorry
