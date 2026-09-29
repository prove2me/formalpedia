-- Prove2me | Theorems.Thm_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jH_quotient_periodLatticeOf_complexConjugation
-- name    : ModularCurve.exists_injective_heckeEquivariant_addMonoidHom_jH_quotient_periodLatticeOf_complexConjugation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/1a125dfa-cc03-5c55-bb0f-896d281e1421
-- title:
--   Uniformisation of J_H(M) with Hecke and conjugation compatibility
-- statement:
--   Let $M$ be a nonzero natural number and $H\le(\mathbb{Z}/M)^\times$ a subgroup, and write $\Gamma_H(M)$ for the subgroup [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) of $\mathrm{SL}(2,\mathbb{Z})$, the image of the preimage of $H$ under the lower-right-entry character $\Gamma_0(M)\to(\mathbb{Z}/M)^\times$. Let $\Lambda=$ [`ModularCurve.periodLatticeOf (CohCarrier.GammaH M H)`](def/ModularCurve_PeriodOf.html#L65) be the $\mathbb{Z}$-submodule of $\mathrm{Dual}_{\mathbb{C}}(\mathrm{CuspForm}(\Gamma_H(M),2))$ spanned by the range of `periodOf`, and let $J_H(M)$ be the group of degree-zero divisor classes of the function field `xHFunctionFieldBar M H` over $\overline{\mathbb{Q}}$. Assume `HeckeDiamondInputsHAll M H`: for every prime $\ell$ the predicate `HeckeInputsHAlong (AlgebraicClosure ℚ) M H ℓ` holds, and for each $d\in(\mathbb{Z}/M)^\times$ there is an $\overline{\mathbb{Q}}$-algebra automorphism $\sigma$ of that function field with `IsDiamondAutHBar M H d σ`. Assume further that $\Lambda$ is stable under the transposes of `heckeTLinH 2` for primes $\ell\nmid M$, of `heckeULinH 2 q` for primes $q\mid M$, and of `diamondLinH 2 d` for all $d$, and that $\Lambda$ is stable in the following sense: if $\varphi\in\Lambda$ and $\varphi'$ satisfies $\varphi'(g)=-\overline{\varphi(f)}$ for all weight-two cusp forms $f,g$ with $g(\tau)=\overline{f(J\cdot\tau)}$ for all $\tau$ in the upper half-plane, then $\varphi'\in\Lambda$. Then there exists an additive homomorphism $u\colon J_H(M)\to \mathrm{Dual}_{\mathbb{C}}(\mathrm{CuspForm}(\Gamma_H(M),2))/\Lambda$ which is injective, whose range contains every element of finite additive order, and which is compatible with the operators in the following pointwise form: whenever $u(x)=[\varphi]$, one has $u(\mathrm{heckeOperatorHAlong}\,(\mathrm{AlgebraicClosure}\ \mathbb{Q})\,M\,H\,\ell \,x)=[\,{}^{t}(\mathrm{heckeTLinH}\ 2)\varphi]$ for primes $\ell\nmid M$, $u(\mathrm{heckeOperatorHAlong}\,(\mathrm{AlgebraicClosure}\ \mathbb{Q})\,M\,H\,q\,x)=[\,{}^{t}(\mathrm{heckeULinH}\ 2\ q)\varphi]$ for primes $q\mid M$, $u(\mathrm{diamondHBar}\,M\,H\,d\,x)=[\,{}^{t}(\mathrm{diamondLinH}\ 2\ d)\varphi]$ for $d\in(\mathbb{Z}/M)^\times$, and $u(\mathrm{complexConjugation}\cdot x)=[\varphi']$ for every $\varphi'$ related to $\varphi$ by the relation $\varphi'(g)=-\overline{\varphi(f)}$ above.
--
--   This is the analytic uniformisation of the Jacobian of $X_H(M)$ over $\overline{\mathbb{Q}}$: an embedding of $J_H(M)(\overline{\mathbb{Q}})$ into $S_2(\Gamma_H(M))^{\vee}/H_1$ carrying the torsion, equivariant for $T_\ell$, $U_q$ and the diamond operators, and with the action of complex conjugation on points matched by the involution $f\mapsto\overline{f(J\cdot\tau)}$ on cusp forms; the conjugation clause is stated for the same map $u$ because $u$ is not otherwise pinned down. It is used to transport the Hecke action and the action of complex conjugation to the $p$-adic Tate module of $J_H(M)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jH_quotient_periodLatticeOf_complexConjugation.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_GaloisRep_ComplexConjugation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.exists_injective_heckeEquivariant_addMonoidHom_jH_quotient_periodLatticeOf_complexConjugation
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (hin : ModularCurve.HeckeDiamondInputsHAll M H)
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
    ∃ u : ModularCurve.JH M H →+
        (Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2) ⧸ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H)),
      Function.Injective u ∧
      (∀ y, IsOfFinAddOrder y → y ∈ u.range) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (x : ModularCurve.JH M H)
          (φ : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2)),
        u x = Submodule.Quotient.mk φ →
        u ((haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
            ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ) x) =
          Submodule.Quotient.mk ((CuspForm.heckeTLinH 2 hℓ hℓM).dualMap φ)) ∧
      (∀ (q : ℕ) (hq : q.Prime), q ∣ M → ∀ (x : ModularCurve.JH M H)
          (φ : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2)),
        u x = Submodule.Quotient.mk φ →
        u ((haveI : NeZero q := ⟨hq.ne_zero⟩;
            ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H q) x) =
          Submodule.Quotient.mk ((CuspForm.heckeULinH 2 q).dualMap φ)) ∧
      (∀ (d : (ZMod M)ˣ) (x : ModularCurve.JH M H) (φ : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2)),
        u x = Submodule.Quotient.mk φ →
        u (ModularCurve.diamondHBar M H d x) = Submodule.Quotient.mk ((CuspForm.diamondLinH 2 d).dualMap φ)) ∧
      ∀ (x : ModularCurve.JH M H) (φ φ' : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2)),
        (∀ f g : CuspForm (CohCarrier.GammaH M H) 2,
          (∀ τ : UpperHalfPlane, g τ = (starRingEnd ℂ) (f (UpperHalfPlane.J • τ))) →
            φ' g = -(starRingEnd ℂ) (φ f)) →
        u x = Submodule.Quotient.mk φ →
        u (complexConjugation • x) = Submodule.Quotient.mk φ' := by sorry
