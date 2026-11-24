-- Prove2me | Theorems.Thm_GlobalTheory_InertiaAlmostAll_finite_mem
-- name    : GlobalTheory.InertiaAlmostAll.finite_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:06:13.518311+00:00
-- url     : https://prove2.me/theorems/8370b51d-b344-4527-9b11-9c56c0e50abe
-- title:
--   Inertia Almost All: finite mem
-- statement:
--   The Inertia Almost All construction uses the finite mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FinitePlacesInertiaNotFixingFiniteExtension.lean#L23-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FinitePlacesInertiaNotFixingFiniteExtension.lean#L23-L28

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinitePlacesInertiaNotFixingFiniteExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory GlobalTheory.InertiaAlmostAll

theorem GlobalTheory.InertiaAlmostAll.finite_mem (F : Type) [Field F] [NumberField F] {c : ℤ} (hc : c ≠ 0) :
    {v : HeightOneSpectrum (𝓞 F) | (c : 𝓞 F) ∈ v.asIdeal}.Finite := by sorry
