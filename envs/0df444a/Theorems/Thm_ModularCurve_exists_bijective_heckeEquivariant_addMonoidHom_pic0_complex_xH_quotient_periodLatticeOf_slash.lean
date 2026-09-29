-- Prove2me | Theorems.Thm_ModularCurve_exists_bijective_heckeEquivariant_addMonoidHom_pic0_complex_xH_quotient_periodLatticeOf_slash
-- name    : ModularCurve.exists_bijective_heckeEquivariant_addMonoidHom_pic0_complex_xH_quotient_periodLatticeOf_slash
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/b3096301-c0ef-5be1-b630-c39f199b4700
-- title:
--   Equivariant Abel–Jacobi bijection for X_H(M) over ℂ
-- statement:
--   Let $M$ be a non-zero natural number, $H \le (\mathbb{Z}/M)^\times$ a subgroup and $\Gamma = \Gamma_H(M) \le \mathrm{SL}_2(\mathbb{Z})$ the image in $\Gamma_0(M)$ of the matrices whose lower-right entry reduces into $H$. Write $\Lambda =$ `periodLatticeOf`$(\Gamma)$, the $\mathbb{Z}$-span inside $\mathrm{Hom}_{\mathbb{C}}(S_2(\Gamma),\mathbb{C})$ of the functionals $\gamma \mapsto$ `periodAlongOf` $\Gamma\, I\, (\gamma \cdot I)$, and $C =$ `laurentBaseChange` $\mathbb{C}$ of the $q$-expansion field `xHFunctionField` $M\,H$. Assume: the seven-fold input package `HeckeInputsHAlong` $\mathbb{C}\,M\,H\,\ell$ holds at every prime $\ell$ (so that `heckeOperatorHAlong` is the correspondence $\alpha_*\beta^*$ rather than $0$); the transpose of [`CuspForm.heckeTLinH`](def/CuspForm_HeckeOperatorFormsGammaH.html#L224) $2$ preserves $\Lambda$ for every prime $\ell \nmid M$; and the transpose of [`CuspForm.heckeULinH`](def/CuspForm_HeckeOperatorFormsGammaH.html#L171) $2\,q$ preserves $\Lambda$ for every prime $q \mid M$. Then there is an additive homomorphism $v : \mathrm{Pic}^0_{\mathbb{C}}(C) \to \mathrm{Hom}_{\mathbb{C}}(S_2(\Gamma),\mathbb{C})/\Lambda$ which is bijective and satisfies, in each case in the form ``$v z = [\varphi]$ implies $v(\Phi z) = [\Phi^{\vee}\varphi]$'': (a) $\Phi =$`heckeOperatorHAlong`$\mathbb{C}\,M\,H\,\ell$ against`heckeTLinH`$2$ for primes $\ell \nmid M$; (b) the same operator against`heckeULinH`$2\,q$ for primes $q \mid M$; (c) for $\alpha \in \mathrm{GL}_2(\mathbb{R})$ with $\det \alpha > 0$ and $\alpha T \alpha^{-1} \in \Gamma$, for every $\mathbb{C}$-algebra automorphism $\sigma$ of $C$ satisfying the pull-back condition that for all $k$ and all weight-$k$ modular forms $f,g$ on $\Gamma$ with integral $q$-expansions $p_f,p_g$, $p_g$ giving a non-zero Laurent series, the product of $\sigma(\mathrm{coeffEmb}(p_f/p_g))$ with the $q$-expansion of $g|_k\alpha$ equals that of $f|_k\alpha$, and for every $\mathbb{C}$-linear $P$ on $S_2(\Gamma)$ with $P f = f|_2\alpha^{-1}$ whose transpose preserves $\Lambda$: the action of`SemilinearAut.ofAlgAut`$\sigma$ on $\mathrm{Pic}^0$ corresponds to $P^{\vee}$; (d) under the assumption that $\Lambda$ is stable under the antilinear pairing relation (if $\varphi'(g) = -\overline{\varphi(f)}$ whenever $g(\tau) = \overline{f(J\tau)}$ for all $\tau$, then $\varphi \in \Lambda$ forces $\varphi' \in \Lambda$), the action of`complexConjAlgEquiv` on $\mathrm{Pic}^0$ sends a class with $v z = [\varphi]$ to $[\varphi']$ for any $\varphi'$ so related to $\varphi$.
--
--   This is the complex Abel–Jacobi theorem for the modular curve $X_H(M)$ — Abel's theorem in both directions together with Jacobi inversion, the period lattice being that of $S_2(\Gamma_H(M)) = H^0(X_H(M),\Omega^1)$ — packaged with its compatibilities: the Hecke correspondences on $\mathrm{Pic}^0$ become the transposes of the Hecke operators on cusp forms, automorphisms of the function field induced by positive-determinant real matrices become transposes of the corresponding slash operators, and coefficientwise complex conjugation becomes the conjugation involution on functionals. It is used in the construction of the injection from $\mathrm{Pic}^0$ of the Jacobian-theoretic model into the quotient of the dual of $S_2$ by the period lattice that is equivariant for the level automorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_bijective_heckeEquivariant_addMonoidHom_pic0_complex_xH_quotient_periodLatticeOf_slash.lean

import Mathlib
import Definitions.Def_ModularCurve_XHHeckeOperator
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_GaloisRep_ComplexConjugation
import Definitions.Def_AlgebraicCurve_BaseChangeGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularCurve.exists_bijective_heckeEquivariant_addMonoidHom_pic0_complex_xH_quotient_periodLatticeOf_slash
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (hinC : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
      ModularCurve.HeckeInputsHAlong ℂ M H ℓ)
    (hstT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H),
      (CuspForm.heckeTLinH 2 hℓ hℓM).dualMap v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H))
    (hstU : ∀ (q : ℕ), q.Prime → q ∣ M → ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H),
      (CuspForm.heckeULinH 2 q).dualMap v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H)) :
    ∃ v : AlgebraicCurve.Pic0 ℂ ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)) →+
        (Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2) ⧸ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H)),
      Function.Bijective v ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)
          (z : AlgebraicCurve.Pic0 ℂ ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)))
          (φ : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2)),
        v z = Submodule.Quotient.mk φ →
        v ((haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; ModularCurve.heckeOperatorHAlong ℂ M H ℓ) z) =
          Submodule.Quotient.mk ((CuspForm.heckeTLinH 2 hℓ hℓM).dualMap φ)) ∧
      (∀ (q : ℕ) (hq : q.Prime), q ∣ M →
          ∀ (z : AlgebraicCurve.Pic0 ℂ ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)))
          (φ : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2)),
        v z = Submodule.Quotient.mk φ →
        v ((haveI : NeZero q := ⟨hq.ne_zero⟩; ModularCurve.heckeOperatorHAlong ℂ M H q) z) =
          Submodule.Quotient.mk ((CuspForm.heckeULinH 2 q).dualMap φ)) ∧
      (∀ (α : GL (Fin 2) ℝ), 0 < (α.det : ℝ) →
          α * (ModularGroup.T : GL (Fin 2) ℝ) * α⁻¹ ∈ (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) →
        ∀ (σ : ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)) ≃ₐ[ℂ]
            ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H))),
        (∀ (k : ℤ) (f g : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
            (pf pg : PowerSeries ℤ) (hf : ModularCurve.IsIntegralQExp f pf) (hg : ModularCurve.IsIntegralQExp g pg)
            (hg0 : ModularCurve.intSeriesC ℚ pg ≠ 0),
            ((σ ⟨ModularCurve.coeffEmb ℂ (ModularCurve.intSeriesC ℚ pf / ModularCurve.intSeriesC ℚ pg),
                  ModularCurve.coeffEmb_mem_laurentBaseChange ℂ
                    (ModularCurve.div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ :
                ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H))) : LaurentSeries ℂ) *
                HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑g ∣[k] α)) =
              HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑f ∣[k] α))) →
        ∀ (P : CuspForm (CohCarrier.GammaH M H) 2 →ₗ[ℂ] CuspForm (CohCarrier.GammaH M H) 2),
          (∀ f : CuspForm (CohCarrier.GammaH M H) 2, ⇑(P f) = ⇑f ∣[(2 : ℤ)] α⁻¹) →
          (∀ w ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H),
            P.dualMap w ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H)) →
        ∀ (z : AlgebraicCurve.Pic0 ℂ ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)))
          (φ : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2)),
          v z = Submodule.Quotient.mk φ →
          v (AlgebraicCurve.SemilinearAut.ofAlgAut σ • z) = Submodule.Quotient.mk (P.dualMap φ)) ∧
      ((∀ (φ φ' : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2)),
          (∀ f g : CuspForm (CohCarrier.GammaH M H) 2,
            (∀ τ : UpperHalfPlane, g τ = (starRingEnd ℂ) (f (UpperHalfPlane.J • τ))) →
              φ' g = -(starRingEnd ℂ) (φ f)) →
          φ ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H) →
            φ' ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H)) →
        ∀ (z : AlgebraicCurve.Pic0 ℂ ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)))
          (φ φ' : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2)),
          (∀ f g : CuspForm (CohCarrier.GammaH M H) 2,
            (∀ τ : UpperHalfPlane, g τ = (starRingEnd ℂ) (f (UpperHalfPlane.J • τ))) →
              φ' g = -(starRingEnd ℂ) (φ f)) →
          v z = Submodule.Quotient.mk φ →
          v (complexConjAlgEquiv • z) = Submodule.Quotient.mk φ') := by sorry
