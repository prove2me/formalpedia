-- Prove2me | Theorems.Thm_GlobalTheory_SmulMemComapLattice_isLattice_comap_subtype
-- name    : GlobalTheory.SmulMemComapLattice.isLattice_comap_subtype
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:57:47.645409+00:00
-- url     : https://prove2.me/theorems/c84d2aec-69eb-46e0-bc45-2fbfaf604847
-- title:
--   Smul Mem Comap Lattice: is Lattice comap subtype
-- statement:
--   The Smul Mem Comap Lattice construction uses the is Lattice comap subtype property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsLatticeComapSubtype.lean#L38-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsLatticeComapSubtype.lean#L38-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLatticeComapSubtype
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SmulMemComapLattice
open NumberField

theorem GlobalTheory.SmulMemComapLattice.isLattice_comap_subtype {K V : Type} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (Λ : Submodule (𝓞 K) V) (hΛ : Submodule.IsLattice K Λ) (W : Submodule K V) :
    Submodule.IsLattice K (Submodule.comap (LinearMap.restrictScalars (𝓞 K) W.subtype) Λ) := by sorry
