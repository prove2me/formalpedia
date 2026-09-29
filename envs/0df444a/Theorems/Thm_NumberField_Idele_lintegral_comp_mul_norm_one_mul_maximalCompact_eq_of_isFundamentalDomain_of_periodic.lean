-- Prove2me | Theorems.Thm_NumberField_Idele_lintegral_comp_mul_norm_one_mul_maximalCompact_eq_of_isFundamentalDomain_of_periodic
-- name    : NumberField.Idele.lintegral_comp_mul_norm_one_mul_maximalCompact_eq_of_isFundamentalDomain_of_periodic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/715816ee-7a4d-5076-a012-e473899d17b5
-- title:
--   Invariance of the weighted idele × K integral
-- statement:
--   Let $F$ be a number field, $\mathbb A$ its adele ring and $\mathbb A^\times$ the idele group, carrying its Borel $\sigma$-algebra and the Haar measure [`NumberField.Idele.idelicHaar`](def/NumberField_IdeleProductMeasure.html#L391). Let $D \subseteq \mathbb A^\times$ be a measurable set that is a fundamental domain, in the sense of `MeasureTheory.IsFundamentalDomain`, for the action of the subgroup [`M4aHerbrand.principalIdeles`](def/M4aHerbrand_IdeleClassVocab.html#L16) of principal ideles (the range of $F^\times \to \mathbb A^\times$ induced by the structure map) on $\mathbb A^\times$ with respect to that Haar measure. Let $\mathbf K =$ `adelicMaximalCompact F` be the subgroup of $\mathrm{GL}_2(\mathbb A)$ consisting of those $k$ whose finite component lies in `finiteIntegralGL2` and whose archimedean component at every infinite place $w$ of $F$ satisfies `IsRowIsometry` (determinant of absolute value $1$, and the displayed quadratic identity on rows), equipped with the Haar measure `maximalCompactHaar F` of its top subgroup. Let $f : \mathbb A^\times \times \mathbf K \to [0,\infty]$ be measurable and satisfy $f(\gamma t, k) = f(t, k)$ for every principal idele $\gamma$, every $t$ and every $k$. Let $c \in \mathbb A^\times$ have [`NumberField.TateGlobal.ideleNorm F c`](def/NumberField_TateGlobalZeta.html#L19) $= 1$, i.e. the distributive Haar character of $\mathbb A$ at $c$ equals $1$, and let $b \in \mathbf K$. Then the lower Lebesgue integrals of $p \mapsto f(p_1 c,\, b p_2)$ and of $f$ against the product of (Haar restricted to $D$, given the density $t \mapsto \mathrm{ofReal}(\|t\|^{-1})$ in the idele norm) with `maximalCompactHaar F` agree.
--
--   This is the change of variables underlying averaging arguments in the $\mathbb A^\times \times \mathbf K$ coordinates: the weighted measure $\|t\|^{-1}\,d^\times t|_D \otimes dk$ on the idele class quotient times the maximal compact subgroup is invariant under right translation by a norm-one idele in the first variable and by an element of $\mathbf K$ in the second. It is used by [`AutomorphicForm.exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile`](thm.html#AutomorphicForm.exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_Idele_lintegral_comp_mul_norm_one_mul_maximalCompact_eq_of_isFundamentalDomain_of_periodic.lean

import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_CarrierPins
import Mathlib.Analysis.Meromorphic.NormalForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm
open scoped NNReal ENNReal Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

theorem NumberField.Idele.lintegral_comp_mul_norm_one_mul_maximalCompact_eq_of_isFundamentalDomain_of_periodic
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdeleRing (𝓞 F) F)ˣ) (_hDm : MeasurableSet D)
    (_hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
    (f : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) → ℝ≥0∞) (_hf : Measurable f)
    (_hper : ∀ γ : (AdeleRing (𝓞 F) F)ˣ, γ ∈ M4aHerbrand.principalIdeles (𝓞 F) F →
      ∀ (t : (AdeleRing (𝓞 F) F)ˣ) (k : ↥(adelicMaximalCompact F)), f (γ * t, k) = f (t, k))
    (c : (AdeleRing (𝓞 F) F)ˣ) (_hc : NumberField.TateGlobal.ideleNorm F c = 1)
    (b : ↥(adelicMaximalCompact F)) :
    ∫⁻ p, f (p.1 * c, b * p.2)
        ∂((((NumberField.Idele.idelicHaar F).restrict D).withDensity
            (fun t : (AdeleRing (𝓞 F) F)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹))).prod
          (maximalCompactHaar F)) =
      ∫⁻ p, f p
        ∂((((NumberField.Idele.idelicHaar F).restrict D).withDensity
            (fun t : (AdeleRing (𝓞 F) F)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹))).prod
          (maximalCompactHaar F)) := by sorry
