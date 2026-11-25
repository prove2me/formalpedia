-- Prove2me | Theorems.Thm_GlobalTheory_T_generalLinear_transitive_on_lattices_over_DVR
-- name    : GlobalTheory.T.generalLinear_transitive_on_lattices_over_DVR
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:33:30.284504+00:00
-- url     : https://prove2.me/theorems/4c444822-1382-43e6-b0e4-b85c59ea782e
-- title:
--   T: general Linear transitive on lattices over DVR
-- statement:
--   The T construction uses the general Linear transitive on lattices over DVR property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/GeneralLinearTransitiveOnLatticesOverDVRStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/GeneralLinearTransitiveOnLatticesOverDVRStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_GeneralLinearTransitiveOnLatticesOverDVR
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_FiniteResidueFieldPadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_GeneralLinearTransitiveOnLatticesOverDVRStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.LatHecke
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.generalLinear_transitive_on_lattices_over_DVR : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ), (∀ L : Lat O K r, ∃ g : GL (Fin r) K, glMap g (std O K r).1 = L.1) ∧ ∀ (g : GL (Fin r) K) (L : Lat O K r), (glMap g L.1).IsLattice K := by sorry
