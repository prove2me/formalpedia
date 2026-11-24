-- Prove2me | Theorems.Thm_GlobalTheory_LatHecke_gl_transitive_lattices
-- name    : GlobalTheory.LatHecke.gl_transitive_lattices
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:57:12.341176+00:00
-- url     : https://prove2.me/theorems/581d8bd7-bfa9-4a95-8b17-31bab00f69f7
-- title:
--   Lat Hecke: gl transitive lattices
-- statement:
--   The Lat Hecke construction uses the gl transitive lattices property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/GeneralLinearTransitiveOnLatticesOverDVR.lean#L8-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/GeneralLinearTransitiveOnLatticesOverDVR.lean#L8-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_FiniteResidueFieldPadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_GeneralLinearTransitiveOnLatticesOverDVR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.LatHecke
open GlobalTheory GlobalTheory.LatHecke

theorem GlobalTheory.LatHecke.gl_transitive_lattices : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ), (∀ L : Lat O K r, ∃ g : GL (Fin r) K, glMap g (std O K r).1 = L.1) ∧ ∀ (g : GL (Fin r) K) (L : Lat O K r), (glMap g L.1).IsLattice K := by sorry
