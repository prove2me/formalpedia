-- Prove2me | Theorems.Thm_ModularCurve_CharPModel_FibreModel_placeFullC_eq_congr_spPlace_of_infChart_centrePin_of_mem_maximalIdeal
-- name    : ModularCurve.CharPModel.FibreModel.placeFullC_eq_congr_spPlace_of_infChart_centrePin_of_mem_maximalIdeal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/365767f9-dad2-5952-98e5-1f7dfd5c5ef9
-- title:
--   Centre-pinned specialisation of places on the pole chart at a cusp
-- statement:
--   Fix $p \ge 1$ and a prime $\ell$ with $\ell \nmid p$, a valuation subring $A$ of $\overline{\mathbb{Q}}$ with $\ell$ a nonunit of $A$ and with algebraically closed residue field $\kappa$ of characteristic $\ell$, together with a ring homomorphism $\rho$ from the subring of rationals with denominator coprime to $\ell$ into $A$ compatible with the inclusion $A \subseteq \overline{\mathbb{Q}}$. Assume given, for every $d \mid p$, a datum `ModularPolynomialData d` (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(d)$ vanishing at $(j, j_d)$), such that for $d = p$ the reduction of $\Phi$ modulo $\ell$ is separable over $\kappa(X)$, and assume the equality $hCF$ of intermediate fields $\kappa(\tilde\jmath, \tilde\jmath_p) = \kappa(\tilde\jmath_d : d \mid p)$ inside $\kappa((q))$. Let `fm` be a fibre model of level $p$ over $A$ with residue field $\kappa$, satisfying the cusp-chart condition that $\tilde\jmath_p \cdot \tilde\jmath^{-p}$ lies in its pole-chart ring $B_\infty$ with the expected image under $\pi_\infty$, and suppose the images under the coefficient embedding of the integral closures $\mathcal{O}_{\mathrm{fin}}$ of $\mathbb{Z}_{(\ell)}[j]$ and $\mathcal{O}_\infty$ of $\mathbb{Z}_{(\ell)}[j^{-1}]$ in the full modular function field lie in $B_{\mathrm{fin}}$, resp. $B_\infty$. Let $w$ be a place of $\overline{\mathbb{Q}}\,(X_0(p))$ (a proper valuation subring containing the constants and a principal ideal ring), $v$ a place of $\kappa(\tilde\jmath_d : d \mid p)$, and $\alpha \colon \mathcal{O}_\infty \to A$ a ring homomorphism with $\alpha(j^{-1})$ in the maximal ideal of $A$. Assume that for every $b \in \mathcal{O}_\infty$ one has $b \in \mathcal{O}_w$ and $b - \alpha(b) \in \mathfrak{m}_w$, and likewise $\pi_\infty(b) \in \mathcal{O}_v$ and $\pi_\infty(b) - \overline{\alpha(b)} \in \mathfrak{m}_v$, the images of $\pi_\infty(b)$ being taken through the inclusion given by $hCF$. Then $v$ is the transport along the ring isomorphism determined by $hCF$ (which fixes $\kappa$) of the specialisation `fm.spPlace` of $w$, formed from the surjectivity of the residue map of $A$, the data $\Phi$ and the separability hypothesis.
--
--   This is the scheme-free core, in the pole chart $\mathbb{Z}_{(\ell)}[j^{-1}]$ and at points reducing to the cusp $j = \infty$, of the compatibility between reduction of $A$-valued points of $X_0(p)$ and specialisation of places: a place $w$ of the generic fibre centred at an $A$-point and a place $v$ of the special fibre centred at its reduction must correspond under the fibre model's specialisation map. It is used by [`ModularCurve.IgusaScheme.pointReduction_eq_congr_spPlace_of_cuspChart_centrePin`](thm.html#ModularCurve.IgusaScheme.pointReduction_eq_congr_spPlace_of_cuspChart_centrePin), the version phrased for points of the Igusa scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_CharPModel_FibreModel_placeFullC_eq_congr_spPlace_of_infChart_centrePin_of_mem_maximalIdeal.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_ReductionOfPointsAgreesModL
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_FibreModel
import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_AlgebraicCurve_CurveModelConstruction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  ModularCurve ModularCurve.CharPModel AlgebraicCurve IsLocalRing ModularCurve.IgusaScheme

open scoped TensorProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.CharPModel.FibreModel.placeFullC_eq_congr_spPlace_of_infChart_centrePin_of_mem_maximalIdeal
    (p : ℕ) [NeZero p] (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ¬ ℓ ∣ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    [CharP (ResidueField ↥A) ℓ] [IsAlgClosed (ResidueField ↥A)]
    (ρ : ↥(GaloisRep.ratLocalizedAt ℓ) →+* ↥A)
    (hρ : A.subtype.comp ρ = algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ p → ModularPolynomialData d)
    (hsep : (((dataAll p (dvd_refl p)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom (ResidueField ↥A)))).map
      (algebraMap (Polynomial (ResidueField ↥A)) (RatFunc (ResidueField ↥A)))).Separable)
    (hCF : modularFunctionFieldC (ResidueField ↥A) p = modularFunctionFieldFullC (ResidueField ↥A) p)
    (fm : FibreModel p A ℓ (ResidueField ↥A) (IsLocalRing.residue ↥A)) (cc : fm.CuspChart)
    (hfin : ∀ b : chartAlgFin p ℓ,
        (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (b : ↥(modularFunctionFieldFull p)).2⟩ :
          laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) ∈ fm.BFin)
    (hinf : ∀ b : chartAlgInf p ℓ,
        (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (b : ↥(modularFunctionFieldFull p)).2⟩ :
          laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) ∈ fm.BInf)
    (w : AlgebraicCurve.Place (AlgebraicClosure ℚ) (modularFunctionFieldBar p))
    (v : AlgebraicCurve.Place (ResidueField ↥A) ↥(modularFunctionFieldFullC (ResidueField ↥A) p))
    (α : ↥(chartAlgInf p ℓ) →+* ↥A)
    (hpole : α (ModularCurve.IgusaScheme.jInvChartInf p ℓ) ∈ IsLocalRing.maximalIdeal ↥A)
    (hgen : ∀ b : ↥(chartAlgInf p ℓ),
          (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (b : ↥(modularFunctionFieldFull p)).2⟩ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) ∈ w.toValuationSubring ∧
          (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (b : ↥(modularFunctionFieldFull p)).2⟩ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) -
              algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) ((A.subtype.comp α) b) ∈
            w.toValuationSubring.nonunits)
    (hsp : ∀ b : ↥(chartAlgInf p ℓ),
          (IntermediateField.inclusion (modularFunctionFieldC_le_full (ResidueField ↥A) p) (fm.piInf ⟨_, hinf b⟩) : ↥(modularFunctionFieldFullC (ResidueField ↥A) p)) ∈
            v.toValuationSubring ∧
          (IntermediateField.inclusion (modularFunctionFieldC_le_full (ResidueField ↥A) p) (fm.piInf ⟨_, hinf b⟩) : ↥(modularFunctionFieldFullC (ResidueField ↥A) p)) -
              algebraMap (ResidueField ↥A) ↥(modularFunctionFieldFullC (ResidueField ↥A) p) (((IsLocalRing.residue ↥A).comp α) b) ∈
            v.toValuationSubring.nonunits) :
    v =
      AlgebraicCurve.Place.congrRingEquiv
        (e := (IntermediateField.equivOfEq hCF).toRingEquiv)
        (he := fun a => (IntermediateField.equivOfEq hCF).commutes a)
        (fm.spPlace Ideal.Quotient.mk_surjective dataAll hsep w) := by sorry
