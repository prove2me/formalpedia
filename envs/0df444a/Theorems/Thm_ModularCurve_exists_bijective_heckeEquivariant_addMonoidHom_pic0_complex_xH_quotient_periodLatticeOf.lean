-- Prove2me | Theorems.Thm_ModularCurve_exists_bijective_heckeEquivariant_addMonoidHom_pic0_complex_xH_quotient_periodLatticeOf
-- name    : ModularCurve.exists_bijective_heckeEquivariant_addMonoidHom_pic0_complex_xH_quotient_periodLatticeOf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/0d8c6118-a109-542a-bf6a-23a324b7ff01
-- title:
--   Hecke-equivariant Abel–Jacobi isomorphism for X_H(M) over ℂ
-- statement:
--   Let $M\ge 1$ and let $H\le(\mathbb{Z}/M)^\times$, and write $\Gamma=\Gamma_H(M)$ for the subgroup of $\Gamma_0(M)\subseteq\mathrm{SL}_2(\mathbb{Z})$ whose lower-right entry reduces into $H$. Let $F$ be the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the ratios of integral $q$-expansions of modular forms of one weight on $\Gamma$, and let $\mathbb{C}F=$ `laurentBaseChange ℂ` $F$ be the subfield of $\mathbb{C}((q))$ generated over $\mathbb{C}$ by the coefficientwise image of $F$; $\mathrm{Pic}^0_\mathbb{C}(\mathbb{C}F)$ is the group of degree-zero divisors on the places of $\mathbb{C}F$ over $\mathbb{C}$ modulo principal ones. Let $\Lambda=$ `periodLatticeOf` $\Gamma$ be the $\mathbb{Z}$-span in $\mathrm{Hom}_\mathbb{C}(S_2(\Gamma),\mathbb{C})$ of the periods $\int_{I}^{\gamma I}$, $\gamma\in\Gamma$. Assume: (i) for every prime $\ell$ the predicate `HeckeInputsHAlong ℂ M H ℓ` holds, namely that the degeneracy map $q\mapsto q^{\ell}$ lands in the level-$M\ell$ function field, that the two resulting algebra maps into $\mathbb{C}\cdot F(\Gamma\cap\Gamma_0(M\ell))$ are integral, that that field has principal divisors, that the extension along $\alpha$ is finite, and that the fundamental identity for $\beta$ and the pushforward norm formula for $\alpha$ hold, so that `heckeOperatorHAlong ℂ M H ℓ` is the correspondence $\alpha_*\beta^*$ on $\mathrm{Pic}^0$; (ii) $\Lambda$ is stable under the transposes of `heckeTLinH` $2$ for primes $\ell\nmid M$, of `heckeULinH` $2\,q$ for primes $q\mid M$ (each being the corresponding weight-$2$ Hecke endomorphism of $S_2(\Gamma)$ when the relevant stability predicate holds and $0$ otherwise), and of `diamondLinH` $2\,d$ for $d\in(\mathbb{Z}/M)^\times$ (the slash action of a lift of $d$ when `StableD` holds, else $0$); (iii) $\Lambda$ is stable under conjugation in the following sense: if $\varphi\in\Lambda$ and $\varphi'$ satisfies $\varphi'(g)=-\overline{\varphi(f)}$ for all $f,g\in S_2(\Gamma)$ with $g(\tau)=\overline{f(J\tau)}$, then $\varphi'\in\Lambda$. Then there is a bijective additive homomorphism $v:\mathrm{Pic}^0_\mathbb{C}(\mathbb{C}F)\to \mathrm{Hom}_\mathbb{C}(S_2(\Gamma),\mathbb{C})/\Lambda$ such that, whenever $v(z)=[\varphi]$: $v$ carries `heckeOperatorHAlong ℂ M H ℓ`$(z)$ to $[\,^{t}T_\ell\varphi]$ for primes $\ell\nmid M$ and to $[\,^{t}U_q\varphi]$ for primes $q\mid M$; for $d\in(\mathbb{Z}/M)^\times$ and any $\mathbb{C}$-algebra automorphism $\sigma$ of $\mathbb{C}F$ satisfying the diamond characterisation — for all $k$, all weight-$k$ forms $f,g$ on $\Gamma$ with integral $q$-expansions $p_f,p_g$, $p_g\neq 0$ in $\mathbb{Q}((q))$, and all $\gamma\in\Gamma_0(M)$ with upper-left entry $\equiv d\pmod M$, one has $\sigma(p_f/p_g)\cdot q\text{-exp}(g\mid_k\gamma)=q\text{-exp}(f\mid_k\gamma)$ — the action of $\sigma$ through `SemilinearAut.ofAlgAut` sends $z$ to a class $v$-equal to $[\,^{t}\langle d\rangle\varphi]$; and the action of [`complexConjAlgEquiv`](def/GaloisRep_ComplexConjugation.html#L22) sends $z$ to a class $v$-equal to $[\varphi']$ for any $\varphi'$ related to $\varphi$ by the conjugation relation of (iii).
--
--   This is the Abel–Jacobi theorem for the compact Riemann surface $X_H(M)(\mathbb{C})$, in the form of an isomorphism of the degree-zero divisor class group of its function field with $\mathrm{Hom}_\mathbb{C}(S_2(\Gamma_H(M)),\mathbb{C})$ modulo the period lattice, compatible with Hecke correspondences, diamond automorphisms and complex conjugation. It is the source of the Hecke-equivariant maps used in the statements about the Jacobian of $X_H$ that construct injective period maps, including the one recording the effect of complex conjugation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_bijective_heckeEquivariant_addMonoidHom_pic0_complex_xH_quotient_periodLatticeOf.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_GaloisRep_ComplexConjugation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularCurve.exists_bijective_heckeEquivariant_addMonoidHom_pic0_complex_xH_quotient_periodLatticeOf
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (hinC : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
      ModularCurve.HeckeInputsHAlong ℂ M H ℓ)
    (hstT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H),
      (CuspForm.heckeTLinH 2 hℓ hℓM).dualMap v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H))
    (hstU : ∀ (q : ℕ), q.Prime → q ∣ M → ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H),
      (CuspForm.heckeULinH 2 q).dualMap v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H))
    (hstD : ∀ (d : (ZMod M)ˣ), ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H),
      (CuspForm.diamondLinH 2 d).dualMap v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H))
    (hstC : ∀ (φ φ' : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2)),
      (∀ f g : CuspForm (CohCarrier.GammaH M H) 2,
        (∀ τ : UpperHalfPlane, g τ = (starRingEnd ℂ) (f (UpperHalfPlane.J • τ))) →
          φ' g = -(starRingEnd ℂ) (φ f)) →
      φ ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H) →
        φ' ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H)) :
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
      (∀ (d : (ZMod M)ˣ)
          (σ : ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)) ≃ₐ[ℂ]
            ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H))),
        (∀ (k : ℤ) (f g : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
            (pf pg : PowerSeries ℤ) (hf : ModularCurve.IsIntegralQExp f pf) (hg : ModularCurve.IsIntegralQExp g pg)
            (hg0 : ModularCurve.intSeriesC ℚ pg ≠ 0) (γ : SL(2, ℤ)),
            γ ∈ CongruenceSubgroup.Gamma0 M → ((γ 0 0 : ℤ) : ZMod M) = (d : ZMod M) →
            ((σ ⟨ModularCurve.coeffEmb ℂ (ModularCurve.intSeriesC ℚ pf / ModularCurve.intSeriesC ℚ pg),
                  ModularCurve.coeffEmb_mem_laurentBaseChange ℂ
                    (ModularCurve.div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ :
                ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H))) : LaurentSeries ℂ) *
                HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑g ∣[k] (γ : GL (Fin 2) ℝ))) =
              HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑f ∣[k] (γ : GL (Fin 2) ℝ)))) →
        ∀ (z : AlgebraicCurve.Pic0 ℂ ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)))
          (φ : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2)),
          v z = Submodule.Quotient.mk φ →
          v (AlgebraicCurve.SemilinearAut.ofAlgAut σ • z) =
            Submodule.Quotient.mk ((CuspForm.diamondLinH 2 d).dualMap φ)) ∧
      ∀ (z : AlgebraicCurve.Pic0 ℂ ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)))
        (φ φ' : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2)),
        (∀ f g : CuspForm (CohCarrier.GammaH M H) 2,
          (∀ τ : UpperHalfPlane, g τ = (starRingEnd ℂ) (f (UpperHalfPlane.J • τ))) →
            φ' g = -(starRingEnd ℂ) (φ f)) →
        v z = Submodule.Quotient.mk φ →
        v (complexConjAlgEquiv • z) = Submodule.Quotient.mk φ' := by sorry
