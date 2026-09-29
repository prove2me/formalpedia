-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_LevelData_isFinite_schemeKerStr_special_and_finrank_eq_pow_two_mul_genusFF_of_abelianSchemePropertyBundle
-- name    : ModularCurve.JHNeronObjectAtP.LevelData.isFinite_schemeKerStr_special_and_finrank_eq_pow_two_mul_genusFF_of_abelianSchemePropertyBundle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/8b2905a0-e38e-50a2-a1a7-0d92229e2d41
-- title:
--   Special m-kernel of the level-(M/p,H') abelian scheme has degree m^{2g'}
-- statement:
--   Let $p$ be a prime and $M>0$ with $p \mid M$ but $p^2 \nmid M$, let $H \le (\mathbb{Z}/M)^\times$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $A$, whose residue field $\kappa$ is algebraically closed of characteristic $p$. Let $\Lambda$ be level data for $p,M,H,A$: a morphism $\sigma_A \colon \operatorname{Spec} A \to \operatorname{Spec} \mathbb{Z}_{(p)}$ (where $\mathbb{Z}_{(p)}$ is the subring of rationals whose denominator is coprime to $p$) lifting the generic point, a scheme $X$ with structure morphism $f \colon X \to \operatorname{Spec} \mathbb{Z}_{(p)}$, a relative group law $L$ on $f$, and bijections of $\operatorname{Pic}^0$ groups with the generic and special fibre point sets of $f$. Assume $f$ is smooth and proper with connected fibres and admits a relative group law, that $L$ is commutative, and that there is a bijection from $J_{H'}(M/p) = \operatorname{Pic}^0$ of the base-changed function field of $X_{H'}(M/p)$, with $H'$ the image of $H$ in $(\mathbb{Z}/(M/p))^\times$, onto the $\overline{\mathbb{Q}}$-points of $f$ which carries addition to the group law. Then for every $m>0$ the structure morphism to $\operatorname{Spec}\kappa$ of the $m$-kernel of the group law obtained by base change along $\operatorname{Spec}\kappa \to \operatorname{Spec} A \to \operatorname{Spec}\mathbb{Z}_{(p)}$ is finite, and the $\kappa$-dimension of the global sections of that kernel equals $m^{2g'}$, where $g'$ is the genus of the field generated over $\kappa$ by ratios of integral $q$-expansions of modular forms for $\Gamma_{H'}(M/p)$.
--
--   This is the degree computation for multiplication by $m$ on an abelian scheme, applied to the level-$(M/p,H')$ member of the Néron-object pair attached to $J_H(M)$ at $p$: the special $m$-torsion is a finite $\kappa$-scheme whose algebra of functions has rank $m^{2g'}$, including when $p \mid m$, the genus in characteristic $p$ being the characteristic-zero genus of $X_{H'}(M/p)$. It is used in the variant of this statement formulated for data representing the relative $\operatorname{Pic}^0$, and thereby in the analysis of the reduction of $J_H(M)$ at $p$ underlying level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_LevelData_isFinite_schemeKerStr_special_and_finrank_eq_pow_two_mul_genusFF_of_abelianSchemePropertyBundle.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_XH
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve
  IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP

theorem ModularCurve.JHNeronObjectAtP.LevelData.isFinite_schemeKerStr_special_and_finrank_eq_pow_two_mul_genusFF_of_abelianSchemePropertyBundle
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A)
    (hΛab : AbelianSchemePropertyBundle (baseRing p) Λ.f)
    (hΛc : Λ.L.IsCommutative)
    (pts : ModularCurve.JH (M / p) (ModularCurve.infSubgroup p M H hpM) ≃ SchemeHomOver (genPt p) Λ.f)
    (hpts : ∀ x y : ModularCurve.JH (M / p) (ModularCurve.infSubgroup p M H hpM), pts (x + y) = Λ.L.mul _ (pts x) (pts y))
    (m : ℕ) (hm : 0 < m) :
    IsFinite ((Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m) ∧
    (letI := Scheme.TwoAffineOpenCover.algebraOfHom ((Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m) ⊤
     Module.finrank (ResidueField ↥A) Γ((Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeKer m, ⊤) =
       m ^ (2 * genusFF (ResidueField ↥A)
         ↥(ModularCurve.qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))))) := by sorry
