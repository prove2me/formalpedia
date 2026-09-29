-- Prove2me | Theorems.Thm_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jH_quotient_periodLatticeOf
-- name    : ModularCurve.exists_injective_heckeEquivariant_addMonoidHom_jH_quotient_periodLatticeOf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/1cd13885-7215-54f8-9de8-194bbed348b9
-- title:
--   Hecke-equivariant embedding of J_H(M) into the analytic Jacobian
-- statement:
--   Let $M$ be a nonzero natural number and $H$ a subgroup of $(\mathbb{Z}/M)^\times$, and write $\Gamma_H(M)$ for the subgroup [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) of $\mathrm{SL}_2(\mathbb{Z})$ consisting of those $\gamma \in \Gamma_0(M)$ whose image under the homomorphism [`CohCarrier.gamma0Units`](def/CohCarrier_Level.html#L121) to $(\mathbb{Z}/M)^\times$ lies in $H$. Assume [`ModularCurve.HeckeDiamondInputsHAll M H`](def/ModularCurve_XHOperators.html#L113), i.e. that [`ModularCurve.HeckeInputsHAlong (AlgebraicClosure ℚ) M H ℓ`](def/ModularCurve_XHHeckeOperator.html#L186) holds for every prime $\ell$ and that for every $d \in (\mathbb{Z}/M)^\times$ there is an $\overline{\mathbb{Q}}$-algebra automorphism $\sigma$ of [`ModularCurve.xHFunctionFieldBar M H`](def/ModularCurve_XH.html#L123) with [`ModularCurve.IsDiamondAutHBar M H d σ`](def/ModularCurve_XHOperators.html#L18). Assume further that the period lattice $\Lambda =$ [`ModularCurve.periodLatticeOf (CohCarrier.GammaH M H)`](def/ModularCurve_PeriodOf.html#L65), the $\mathbb{Z}$-span inside $\mathrm{Hom}_{\mathbb{C}}(S_2(\Gamma_H(M)),\mathbb{C})$ of the range of [`ModularCurve.periodOf`](def/ModularCurve_PeriodOf.html#L56), is stable under the transposes of the weight-$2$ operators [`CuspForm.heckeTLinH 2`](def/CuspForm_HeckeOperatorFormsGammaH.html#L224) for primes $\ell \nmid M$, [`CuspForm.heckeULinH 2 q`](def/CuspForm_HeckeOperatorFormsGammaH.html#L171) for primes $q \mid M$, and [`CuspForm.diamondLinH 2 d`](def/CuspForm_HeckeOperatorFormsGammaH.html#L132) for $d \in (\mathbb{Z}/M)^\times$ (each of these linear maps being defined as the corresponding Hecke or diamond operator when the relevant stability predicate `StableT`, `StableU`, `StableD` holds, and as $0$ otherwise). Then there exists an additive homomorphism $u$ from $J_H(M) =$ [`ModularCurve.JH M H`](def/ModularCurve_XH.html#L127), the group of degree-zero divisor classes of `xHFunctionFieldBar M H` over $\overline{\mathbb{Q}}$ modulo principal divisors, to the quotient $\mathrm{Hom}_{\mathbb{C}}(S_2(\Gamma_H(M)),\mathbb{C})/\Lambda$ such that: $u$ is injective; every element of finite additive order of the quotient lies in the range of $u$; and $u$ intertwines the arithmetic operators with the analytic transposes, in the sense that whenever $u(x)$ is the class of $\varphi$, the image under $u$ of [`ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ`](def/ModularCurve_XHHeckeOperator.html#L195) applied to $x$ is the class of $(\mathtt{heckeTLinH } 2\,\ell)^{\vee}\varphi$ for $\ell$ prime with $\ell \nmid M$, the image under $u$ of the same operator at a prime $q \mid M$ is the class of $(\mathtt{heckeULinH } 2\, q)^{\vee}\varphi$, and $u(\mathtt{diamondHBar } M\, H\, d\, x)$ is the class of $(\mathtt{diamondLinH } 2\, d)^{\vee}\varphi$.
--
--   This is the analytic uniformisation of the Jacobian of $X_H(M)$ in the form used later: an injective, Hecke- and diamond-equivariant map from the $\overline{\mathbb{Q}}$-points of $J_H(M)$ onto the torsion of $S_2(\Gamma_H(M))^{\vee}/\Lambda$, obtained by composing base change to $\mathbb{C}$ with the Abel–Jacobi isomorphism. It is the source of the comparison between the $p$-adic Tate module of $J_H(M)$ and the Hecke module of periods, and is used for the finiteness of torsion and for linear independence of Hecke eigenvectors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jH_quotient_periodLatticeOf.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_ModularCurve_PeriodOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.exists_injective_heckeEquivariant_addMonoidHom_jH_quotient_periodLatticeOf
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    (hstT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H),
      (CuspForm.heckeTLinH 2 hℓ hℓM).dualMap v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H))
    (hstU : ∀ (q : ℕ), q.Prime → q ∣ M → ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H),
      (CuspForm.heckeULinH 2 q).dualMap v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H))
    (hstD : ∀ (d : (ZMod M)ˣ), ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H),
      (CuspForm.diamondLinH 2 d).dualMap v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H)) :
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
      ∀ (d : (ZMod M)ˣ) (x : ModularCurve.JH M H) (φ : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2)),
        u x = Submodule.Quotient.mk φ →
        u (ModularCurve.diamondHBar M H d x) =
          Submodule.Quotient.mk ((CuspForm.diamondLinH 2 d).dualMap φ) := by sorry
