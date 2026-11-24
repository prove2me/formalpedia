-- Prove2me | Theorems.Thm_GlobalTheory_exists_ker_eq_dehomogenisation
-- name    : GlobalTheory.exists_ker_eq_dehomogenisation
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:33:06.735054+00:00
-- url     : https://prove2.me/theorems/412b199d-0a39-41ed-ae43-5e086b46d238
-- title:
--   Global Theory: exists ker eq dehomogenisation
-- statement:
--   The Global Theory construction uses the exists ker eq dehomogenisation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DehomogenisationIsRadicalAndTorsionFree.lean#L23-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DehomogenisationIsRadicalAndTorsionFree.lean#L23-L106

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DehomogenisationIsRadicalAndTorsionFree
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

theorem GlobalTheory.exists_ker_eq_dehomogenisation {o σ : Type} [CommRing o] (I : Ideal (MvPolynomial σ o))
    (i : σ) (hI : ∀ F ∈ I, ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) :
    ∃ ψ : MvPolynomial σ o →+*
        Localization.Away (Ideal.Quotient.mk I (MvPolynomial.X i)),
      (∀ c, ψ (MvPolynomial.C c) = algebraMap (MvPolynomial σ o ⧸ I) _
        (Ideal.Quotient.mk I (MvPolynomial.C c))) ∧
      RingHom.ker ψ = I ⊔ Ideal.span {MvPolynomial.X i - 1} := by sorry
