-- Prove2me | Theorems.Thm_GlobalTheory_HomogMinPrime_mem_ker_cone
-- name    : GlobalTheory.HomogMinPrime.mem_ker_cone
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T14:38:24.509734+00:00
-- url     : https://prove2.me/theorems/64122b30-804c-4839-ae68-a3437a426f6b
-- title:
--   Homog Min Prime: mem ker cone
-- statement:
--   The Homog Min Prime construction uses the mem ker cone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/KerConeMemMinimalPrimes.lean#L40-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/KerConeMemMinimalPrimes.lean#L40-L64

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_KerConeMemMinimalPrimes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory
open GlobalTheory.HomogMinPrime
open MvPolynomial

theorem GlobalTheory.HomogMinPrime.mem_ker_cone {o σ K : Type} [CommRing o] [Field K] (β : o →+* K) (u : σ → K)
    (F : MvPolynomial σ o) :
    F ∈ RingHom.ker (eval₂Hom ((Polynomial.C : K →+* Polynomial K).comp β)
      (fun a => Polynomial.C (u a) * Polynomial.X)) ↔
      ∀ e, eval₂Hom β u (homogeneousComponent e F) = 0 := by sorry
