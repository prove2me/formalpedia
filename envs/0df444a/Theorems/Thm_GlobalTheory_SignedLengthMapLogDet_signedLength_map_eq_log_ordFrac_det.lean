-- Prove2me | Theorems.Thm_GlobalTheory_SignedLengthMapLogDet_signedLength_map_eq_log_ordFrac_det
-- name    : GlobalTheory.SignedLengthMapLogDet.signedLength_map_eq_log_ordFrac_det
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:54:10.502354+00:00
-- url     : https://prove2.me/theorems/5b863eff-6220-4704-a075-fb009d115d61
-- title:
--   Signed Length Map Log Det: signed Length map eq log ord Frac det
-- statement:
--   The Signed Length Map Log Det construction uses the signed Length map eq log ord Frac det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SignedLengthMapEqLogOrdFracDet.lean#L188-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SignedLengthMapEqLogOrdFracDet.lean#L188-L227

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SignedLengthMapEqLogOrdFracDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2 u_3
open GlobalTheory GlobalTheory.SignedLengthMapLogDet
open Module

theorem GlobalTheory.SignedLengthMapLogDet.signedLength_map_eq_log_ordFrac_det
    {R : Type u_1} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type u_2} [Field K] [Algebra R K] [IsFractionRing R K]
    {V : Type u_3} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    (A : Submodule R V) [Submodule.IsLattice K A] (g : V →ₗ[K] V) (hg : LinearMap.det g ≠ 0) :
    LengthCommensurable A (A.map (g.restrictScalars R)) ∧
      signedLength A (A.map (g.restrictScalars R)) =
        WithZero.log (Ring.ordFrac R (LinearMap.det g)) := by sorry
