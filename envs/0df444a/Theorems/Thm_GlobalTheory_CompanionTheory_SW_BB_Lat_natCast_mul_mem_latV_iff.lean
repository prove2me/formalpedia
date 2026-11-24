-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_BB_Lat_natCast_mul_mem_latV_iff
-- name    : GlobalTheory.CompanionTheory.SW.BB.Lat.natCast_mul_mem_latV_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:01:10.337582+00:00
-- url     : https://prove2.me/theorems/91ef5c63-761b-49c8-a167-08a5c17c7f88
-- title:
--   Lat: nat Cast mul mem lat V iff
-- statement:
--   The Lat construction uses the nat Cast mul mem lat V iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/FiniteAdelicLatticeMembershipIff.lean#L30-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/FiniteAdelicLatticeMembershipIff.lean#L30-L53

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussQ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FiniteAdelicLatticeMembershipIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB GlobalTheory.CompanionTheory.SW.BB.Lat
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem GlobalTheory.CompanionTheory.SW.BB.Lat.natCast_mul_mem_latV_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
    (d M : ℕ) (b : Module.Basis (Fin d) F E) (a : ℕ) (X : Fin 1 → Fin M → Af F ⊗[F] E),
    (∀ v, (fun p i => (a : Fv F v ⊗[F] E) * projV v X p i) ∈ latV b v) ↔
      ∀ i v, ((a : Af F) * cv (Af F) b (X 0) i) v ∈ v.adicCompletionIntegers F := by sorry
