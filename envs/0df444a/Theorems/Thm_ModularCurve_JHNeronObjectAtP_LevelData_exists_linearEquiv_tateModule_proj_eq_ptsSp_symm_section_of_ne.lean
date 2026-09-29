-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_LevelData_exists_linearEquiv_tateModule_proj_eq_ptsSp_symm_section_of_ne
-- name    : ModularCurve.JHNeronObjectAtP.LevelData.exists_linearEquiv_tateModule_proj_eq_ptsSp_symm_section_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/43fe1589-cc96-5999-9c8d-9a45aec7f4d0
-- title:
--   Good reduction identifies ℓ-adic Tate modules for ℓ ≠ p
-- statement:
--   Let $p$ be a prime, $M$ a nonzero natural number with $p \mid M$, $H \le (\mathbb{Z}/M)^\times$ a subgroup, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$, whose residue field $\kappa$ is algebraically closed of characteristic $p$. Let $\Lambda$ be a `LevelData p M H hpM A`: a morphism $\sigma_A \colon \operatorname{Spec} A \to \operatorname{Spec} R_p$, where $R_p =$ `baseRing p` is the subring of $\mathbb{Q}$ of fractions with denominator coprime to $p$, satisfying $\sigma_A \circ \operatorname{Spec}(A \hookrightarrow \overline{\mathbb{Q}})^{\ast} =$ `genPt p`; a scheme $X$ with structure morphism $f \colon X \to \operatorname{Spec} R_p$; a relative group law $L$ on $f$; a bijection $\mathrm{pts}$ from $J_{H'}(M/p) = \operatorname{Pic}^0$ of the function field `xHFunctionFieldBar (M/p) H'` over $\overline{\mathbb{Q}}$, $H'$ the image of $H$ in $(\mathbb{Z}/(M/p))^\times$, onto the $f$-sections over `genPt p`; and a bijection $\mathrm{pts}^{\mathrm{sp}}$ from $\operatorname{Pic}^0$ over $\kappa$ of `Fbar p M H hpM κ` onto the $f$-sections over `resPt A ≫ σA`. Assume $f$ is smooth and proper with connected fibres and admits a relative group law, that $\mathrm{pts}$ is additive for $L$, and that $\mathrm{pts}^{\mathrm{sp}}$ is additive for the base change of $L$ along `resPt A ≫ σA` (transported by `toFibrePt`/`ofFibrePt`). Then, for every prime $\ell \ne p$, there is a $\mathbb{Z}_\ell$-linear isomorphism $sp$ from [`TateModule ℓ`](def/EllipticCurve_TateModule.html#L15) of $J_{H'}(M/p)$ to [`TateModule ℓ`](def/EllipticCurve_TateModule.html#L15) of $\operatorname{Pic}^0_\kappa$, where [`TateModule ℓ N`](def/EllipticCurve_TateModule.html#L15) consists of the sequences $(x_n)$ in $N$ with $\ell^n x_n = 0$ and $\ell x_{n+1} = x_n$, with the following property: whenever $w$ lies in the source, $n \in \mathbb{N}$, and $s \colon \operatorname{Spec} A \to X$ is a morphism with $s \circ f = \sigma_A$ whose restriction along $\operatorname{Spec}\overline{\mathbb{Q}} \to \operatorname{Spec} A$ is the $\overline{\mathbb{Q}}$-point $\mathrm{pts}(w_n)$, then the $n$-th component of $sp(w)$ is the divisor class $(\mathrm{pts}^{\mathrm{sp}})^{-1}$ of the reduction of $s$, that is, of $\operatorname{Spec}\kappa \to \operatorname{Spec} A$ followed by $s$.
--
--   This is the specialisation isomorphism on $\ell$-adic Tate modules of an abelian scheme over a henselian valuation base at a prime $\ell$ invertible in the residue field, in the form needed for the level-$(M/p)$ Jacobian attached to $X_{H'}(M/p)$ at a place above $p$, the compatibility clause pinning down the isomorphism by reduction of sections over $\operatorname{Spec} A$. It feeds the analysis of the $p$-old part of $T_\ell J_H(M)$ inside the Tate module of the Néron model's special fibre, being used in [`ModularCurve.JHNeronObjectAtP.exists_oldLattice_inf_toricLattice_eq_bot_and_finiteLattice_le_sup_tateModule_jH_of_ne`](thm.html#ModularCurve.JHNeronObjectAtP.exists_oldLattice_inf_toricLattice_eq_bot_and_finiteLattice_le_sup_tateModule_jH_of_ne).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_LevelData_exists_linearEquiv_tateModule_proj_eq_ptsSp_symm_section_of_ne.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP

theorem ModularCurve.JHNeronObjectAtP.LevelData.exists_linearEquiv_tateModule_proj_eq_ptsSp_symm_section_of_ne
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A)

    (hΛ : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ.f)

    (hΛpts_add : ∀ x y : JH (M / p) (infSubgroup p M H hpM), Λ.pts (x + y) = Λ.L.mul _ (Λ.pts x) (Λ.pts y))
    (hΛptsSp_add : ∀ x y : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)),
      Λ.ptsSp (x + y) = ofFibrePt ((Λ.L.baseChange (resPt A ≫ Λ.σA)).mul _ (toFibrePt (Λ.ptsSp x)) (toFibrePt (Λ.ptsSp y))))
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p) :
    ∃ sp : TateModule ℓ (JH (M / p) (infSubgroup p M H hpM)) ≃ₗ[ℤ_[ℓ]]
        TateModule ℓ (Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))),

      ∀ (w : TateModule ℓ (JH (M / p) (infSubgroup p M H hpM))) (n : ℕ) (s : SchemeHomOver Λ.σA Λ.f),
        (Λ.pts (TateModule.proj ℓ (JH (M / p) (infSubgroup p M H hpM)) n w)).1 = barPt A ≫ s.1 →
        TateModule.proj ℓ (Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) n (sp w) =
          Λ.ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s) := by sorry
