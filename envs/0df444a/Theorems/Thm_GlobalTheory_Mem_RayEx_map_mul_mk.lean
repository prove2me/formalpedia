-- Prove2me | Theorems.Thm_GlobalTheory_Mem_RayEx_map_mul_mk
-- name    : GlobalTheory.Mem.RayEx.map_mul_mk
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:45:15.445377+00:00
-- url     : https://prove2.me/theorems/7148f439-7dcb-4d2a-8389-468a5cf277a4
-- title:
--   Ray Ex: map mul mk
-- statement:
--   The Ray Ex construction uses the map mul mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RayDataNonempty.lean#L148-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RayDataNonempty.lean#L148-L152

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayDataNonempty
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.RayEx
open NumberField IsDedekindDomain
variable {R : Type} [CommRing R] [IsDedekindDomain R] (m : Ideal R)
variable {m}

theorem GlobalTheory.Mem.RayEx.map_mul_mk {G : Type} [CommGroup G] (φ : S m →* G) {I J : Ideal R} (hI : IsCoprime I m)
    (hJ : IsCoprime J m) : φ ⟨I * J, hI.mul_left hJ⟩ = φ ⟨I, hI⟩ * φ ⟨J, hJ⟩ := by sorry
