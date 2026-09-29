-- Prove2me | Theorems.Thm_NumberField_Idele_withDensity_inv_ideleNorm_restrict_prod_maximalCompactHaar_band_lt_top
-- name    : NumberField.Idele.withDensity_inv_ideleNorm_restrict_prod_maximalCompactHaar_band_lt_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/e878edfa-b6ec-5224-a1fc-1849a9d55b09
-- title:
--   Finite mass of a norm band for ‖t‖⁻¹d^× t⊗ dk
-- statement:
--   Let $F$ be a number field, and equip the unit group $(\mathbb A_F)^\times$ of its adele ring, the adele ring itself and the adelic $\mathrm{GL}_2$ with their Borel structures. Let $D$ be a measurable subset of $(\mathbb A_F)^\times$ which is a fundamental domain, in the sense of `MeasureTheory.IsFundamentalDomain`, for the action of the subgroup [`M4aHerbrand.principalIdeles`](def/M4aHerbrand_IdeleClassVocab.html#L16) — the image of $F^\times$ under the map induced by $F \to \mathbb A_F$ — with respect to the Haar measure [`NumberField.Idele.idelicHaar`](def/NumberField_IdeleProductMeasure.html#L391) on $(\mathbb A_F)^\times$. Let $a', b'$ be real numbers with $0 < a'$; no relation between $a'$ and $b'$ is assumed. Write $\|t\| = \mathrm{ideleNorm}_F(t)$ for the value at $t$ of the distributive Haar character of $\mathbb A_F$, viewed as a real number. Form on $(\mathbb A_F)^\times$ the measure obtained by restricting the idelic Haar measure to $D$ and then taking the density $\mathrm{ofReal}(\|t\|^{-1})$, and on the subgroup `adelicMaximalCompact` of $\mathrm{GL}_2(\mathbb A_F)$ — consisting of those $k$ whose finite part lies in `finiteIntegralGL2` and whose component at each infinite place $w$ is a row isometry, i.e. has determinant of absolute value $1$ and preserves $\|x\|^2+\|y\|^2$ under the indicated row action — the Haar measure of its top subgroup. The assertion is that the product of these two measures gives finite mass to the band $\{(t,k) : \|t\| \in [a',b']\}$.
--
--   This is the finiteness half of the statement that a norm band inside a fundamental domain for $F^\times$ in $\mathbb A_F^\times$ has finite mass for the measure $\|t\|^{-1}d^\times t$ tensored with the Haar probability measure of the adelic maximal compact subgroup. It serves as the integrability input for the approximation of band-supported invariant continuous functions by sums of characters times smooth times $K$-finite functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_Idele_withDensity_inv_ideleNorm_restrict_prod_maximalCompactHaar_band_lt_top.lean

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

theorem NumberField.Idele.withDensity_inv_ideleNorm_restrict_prod_maximalCompactHaar_band_lt_top
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdeleRing (𝓞 F) F)ˣ) (hDm : MeasurableSet D)
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
    (a' b' : ℝ) (ha' : 0 < a') :
    ((((NumberField.Idele.idelicHaar F).restrict D).withDensity
            (fun t : (AdeleRing (𝓞 F) F)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹))).prod
          (maximalCompactHaar F))
        {p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) | NumberField.TateGlobal.ideleNorm F p.1 ∈ Set.Icc a' b'} < ⊤ := by sorry
