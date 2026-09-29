-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_LevelData_isFinite_schemeKerStr_special_and_finrank_eq_pow_two_mul_genusFF_of_representsRelSubPic
-- name    : ModularCurve.JHNeronObjectAtP.LevelData.isFinite_schemeKerStr_special_and_finrank_eq_pow_two_mul_genusFF_of_representsRelSubPic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/151665b4-a9c2-5dac-844b-4b02f559a3e1
-- title:
--   Order of the special p^v-kernel from representability
-- statement:
--   Fix a prime $p$ and a positive integer $M$ with $p \mid M$ and $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing the kernel of the reduction map $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ (every unit sent to $1$ lies in $H$), with $M/p$ nonzero. Let $Pl$ be a valuation subring of an algebraic closure of $\mathbb{Q}$ with $p$ a nonunit of $Pl$, whose residue field is algebraically closed of characteristic $p$; let $hj$ record that the Laurent series `jqModC ℚ` lies in the intermediate field `qExpFunctionFieldC ℚ ⊤` of $\mathbb{Q}$-rational $q$-expansions for $SL(2,\mathbb{Z})$; let $\mathfrak{X}$ be a model bundle `XHDRModelAtP p M H hpM hj`, and let $\Lambda$ be level data `LevelData p M H hpM Pl`, consisting of a section $\sigma_A$ of the base over the $p$-local ring, a scheme $\Lambda.X$ with structure morphism $\Lambda.f$, a relative group law $\Lambda.L$ on $\Lambda.f$, and identifications of the generic and special sections with $J_H$ at level $(M/p, \mathrm{infSubgroup}\,p\,M\,H)$ and with the degree-zero divisor class group of the corresponding function field over the residue field. Assume that the pointed object given by $\Lambda.X$, $\Lambda.f$ and the unit section of $\Lambda.L$ represents, as a `RelativePic0Designation`, the rigidified line bundles on the level-$\Gamma_N$ two-chart integral model `toBase p (ΓN p M H hpM) hj` rigidified along $\mathfrak{X}.\varepsilon_{\inf}$ followed by $\mathfrak{X}.\pi$ and satisfying the condition `algEquivZeroCut`, i.e. fibrewise algebraic equivalence to zero over algebraically closed fields. Then for every $v \in \mathbb{N}$, writing $\kappa$ for the residue field of $Pl$ and base-changing $\Lambda.L$ along `resPt Pl ≫ Λ.σA`: the structure morphism to $\operatorname{Spec}\kappa$ of the kernel of multiplication by $p^v$ (the pullback of the $p^v$-multiplication morphism along the unit section) is finite, and the $\kappa$-vector space of global sections of that kernel scheme, with the algebra structure induced by its structure morphism, has dimension $p^{2 v g'}$, where $g' = \dim_\kappa H^1(0)$ is the genus `genusFF` of the function field `qExpFunctionFieldC κ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))` over $\kappa$.
--
--   This computes the order of the $p^v$-torsion of the special fibre of the abelian part of the Néron model of $J_H(M)$ at $p$, in the form $p^{2vg'}$ with $g'$ the genus of the level-$(M/p, H')$ modular function field over the residue field, assuming only that the level data represents the relative $\operatorname{Pic}^0$ functor cut out by fibrewise algebraic equivalence to zero. It is used in the computations of the finite part of the kernel, of the cardinality of the finite points, and of the height of the Raynaud quotient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_LevelData_isFinite_schemeKerStr_special_and_finrank_eq_pow_two_mul_genusFF_of_representsRelSubPic.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing ModularCurve.XHDRLevel AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open AlgebraicCurve

universe u

theorem ModularCurve.JHNeronObjectAtP.LevelData.isFinite_schemeKerStr_special_and_finrank_eq_pow_two_mul_genusFF_of_representsRelSubPic
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (ResidueField ↥Pl) p] [IsAlgClosed (ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)

    (hrepΛ : Nonempty (RepresentsRelSubPic (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)
          (algEquivZeroCut (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)) (⟨Λ.X, Λ.f, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (XHDRLevel.ΓN p M H hpM) hj))))
    (v : ℕ) :
    IsFinite ((Λ.L.baseChange (ModularCurve.JZeroNeronObjectAtP.resPt Pl ≫ Λ.σA)).schemeKerStr (p ^ v)) ∧
    (letI := Scheme.TwoAffineOpenCover.algebraOfHom ((Λ.L.baseChange (ModularCurve.JZeroNeronObjectAtP.resPt Pl ≫ Λ.σA)).schemeKerStr (p ^ v)) ⊤
     Module.finrank (ResidueField ↥Pl) Γ((Λ.L.baseChange (ModularCurve.JZeroNeronObjectAtP.resPt Pl ≫ Λ.σA)).schemeKer (p ^ v), ⊤) =
       p ^ (2 * v * AlgebraicCurve.genusFF (ResidueField ↥Pl)
         ↥(ModularCurve.qExpFunctionFieldC (ResidueField ↥Pl) (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))))) := by sorry
