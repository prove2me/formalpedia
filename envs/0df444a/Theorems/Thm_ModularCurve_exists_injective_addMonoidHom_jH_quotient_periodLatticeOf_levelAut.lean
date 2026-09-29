-- Prove2me | Theorems.Thm_ModularCurve_exists_injective_addMonoidHom_jH_quotient_periodLatticeOf_levelAut
-- name    : ModularCurve.exists_injective_addMonoidHom_jH_quotient_periodLatticeOf_levelAut
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/1299574f-a5ba-5b48-bfbd-e2de94a6e89e
-- title:
--   Analytic uniformisation of J_H(q²M') with level automorphisms
-- statement:
--   Fix a prime $q$ and $M'\ge 1$, put $M=q^2M'$ and let $H\le(\mathbb Z/M)^\times$ be [`ModularCurve.FullLevel.levelH q M'`](def/ModularCurve_FullLevelJacobian.html#L22), the kernel of reduction $(\mathbb Z/M)^\times\to(\mathbb Z/q)^\times$; write $\Gamma=$ [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) for the associated congruence subgroup of $\mathrm{SL}(2,\mathbb Z)$ and $\Lambda=$ [`ModularCurve.periodLatticeOf`](def/ModularCurve_PeriodOf.html#L65) $\Gamma$ for the $\mathbb Z$-span of the periods inside $\mathrm{Dual}_{\mathbb C}(S_2(\Gamma))$, where $S_2(\Gamma)=$ `CuspForm` $\Gamma\,2$. Assume: `HeckeDiamondInputsHAll M H`, i.e. the input package `HeckeInputsHAlong` over $\overline{\mathbb Q}$ for every prime $\ell$, together with, for each $d\in(\mathbb Z/M)^\times$, an $\overline{\mathbb Q}$-automorphism of the function field `xHFunctionFieldBar M H` satisfying `IsDiamondAutHBar M H d`; that $\Lambda$ is stable under the transposes of [`CuspForm.heckeTLinH 2`](def/CuspForm_HeckeOperatorFormsGammaH.html#L224) for primes $\ell\nmid M$, of [`CuspForm.heckeULinH 2 p`](def/CuspForm_HeckeOperatorFormsGammaH.html#L171) for primes $p\mid M$, and of [`CuspForm.diamondLinH 2 d`](def/CuspForm_HeckeOperatorFormsGammaH.html#L132); and that there is given a family $L_\gamma$ ($\gamma\in\Gamma_0(M')$) of $\mathbb C$-linear endomorphisms of $S_2(\Gamma)$ with $L_\gamma f=f\mid_2(\gamma^\sharp)^{-1}$, where $\gamma^\sharp=$ `conjElem` $q\,\gamma=\mathrm{diag}(q,1)^{-1}\gamma\,\mathrm{diag}(q,1)$, whose transposes also preserve $\Lambda$. The conclusion asserts the existence of an additive map $u$ from `jacComp q M'` $=$ `JH M H` to $\mathrm{Dual}_{\mathbb C}(S_2(\Gamma))/\Lambda$ which is injective, whose range contains every element of finite additive order, and which intertwines: `heckeOperatorHAlong` over $\overline{\mathbb Q}$ at $\ell$ with the transpose of [`CuspForm.heckeTLinH 2`](def/CuspForm_HeckeOperatorFormsGammaH.html#L224) for $\ell\nmid M$ prime; the same operator at $p$ with the transpose of [`CuspForm.heckeULinH 2 p`](def/CuspForm_HeckeOperatorFormsGammaH.html#L171) for $p\mid M$ prime; `diamondHBar M H d` with the transpose of [`CuspForm.diamondLinH 2 d`](def/CuspForm_HeckeOperatorFormsGammaH.html#L132); and, for some $\zeta_0\in$ `Idx q` (a primitive $q$-th root of unity in $\overline{\mathbb Q}$), the action on `JH M H` of `SemilinearAut.ofAlgAut` $\tau$, for every $\gamma\in\Gamma_0(M')$ and every $\overline{\mathbb Q}$-algebra automorphism $\tau$ of `fieldBar q M'` satisfying `IsLevelAutBar q M' ζ₀ γ τ` (that is, $\tau$ acts on quotients of $q$-expansions of weight-$k$ forms by slashing with $\gamma^\sharp$, under any embedding $\overline{\mathbb Q}\hookrightarrow\mathbb C$ carrying $\zeta_0$ to $e^{2\pi i/q}$), with the transpose of $L_\gamma$. Each intertwining is phrased pointwise: if $u(x)$ is the class of $\varphi$, then the value of $u$ on the transformed point is the class of the corresponding transpose applied to $\varphi$.
--
--   This is the analytic uniformisation (Abel–Jacobi together with Jacobi inversion, after base change from $\overline{\mathbb Q}$ to $\mathbb C$) of the Jacobian of the modular curve of level $\Gamma_H(q^2M')$, stated so as to be natural not only for the Hecke and diamond operators but also for the automorphisms of the function field attached to elements of $\Gamma_0(M')$ via conjugation by $\mathrm{diag}(q,1)$. It feeds the description of the $p$-adic Tate module of this Jacobian as a tensor product involving the period lattice, compatibly with the level automorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_injective_addMonoidHom_jH_quotient_periodLatticeOf_levelAut.lean

import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped MatrixGroups ModularForm TensorProduct

theorem ModularCurve.exists_injective_addMonoidHom_jH_quotient_periodLatticeOf_levelAut
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (hin : ModularCurve.HeckeDiamondInputsHAll (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))
    (hstT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ q ^ 2 * M'),
      ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')),
        (CuspForm.heckeTLinH 2 hℓ hℓM).dualMap v ∈
          ModularCurve.periodLatticeOf (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))
    (hstU : ∀ (p : ℕ), p.Prime → p ∣ q ^ 2 * M' →
      ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')),
        (CuspForm.heckeULinH 2 p).dualMap v ∈
          ModularCurve.periodLatticeOf (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))
    (hstD : ∀ (d : (ZMod (q ^ 2 * M'))ˣ),
      ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')),
        (CuspForm.diamondLinH 2 d).dualMap v ∈
          ModularCurve.periodLatticeOf (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))
    (L : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      (CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2 →ₗ[ℂ]
        CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2))
    (hL : ∀ (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M')
      (f : CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2),
      ⇑(L γ hγ f) = ⇑f ∣[(2 : ℤ)] (ModularCurve.FullLevel.conjElem q γ)⁻¹)
    (hstL : ∀ (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M'),
      ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')),
        (L γ hγ).dualMap v ∈
          ModularCurve.periodLatticeOf (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))) :
    ∃ u : ModularCurve.FullLevel.jacComp q M' →+
        (Module.Dual ℂ (CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2) ⧸
          ModularCurve.periodLatticeOf (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))),
      Function.Injective u ∧
      (∀ y, IsOfFinAddOrder y → y ∈ u.range) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ q ^ 2 * M') (x : ModularCurve.FullLevel.jacComp q M')
          (φ : Module.Dual ℂ (CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2)),
        u x = Submodule.Quotient.mk φ →
        u ((haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
            ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) (q ^ 2 * M')
              (ModularCurve.FullLevel.levelH q M') ℓ) x) =
          Submodule.Quotient.mk ((CuspForm.heckeTLinH 2 hℓ hℓM).dualMap φ)) ∧
      (∀ (p : ℕ) (hp : p.Prime), p ∣ q ^ 2 * M' → ∀ (x : ModularCurve.FullLevel.jacComp q M')
          (φ : Module.Dual ℂ (CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2)),
        u x = Submodule.Quotient.mk φ →
        u ((haveI : NeZero p := ⟨hp.ne_zero⟩;
            ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) (q ^ 2 * M')
              (ModularCurve.FullLevel.levelH q M') p) x) =
          Submodule.Quotient.mk ((CuspForm.heckeULinH 2 p).dualMap φ)) ∧
      (∀ (d : (ZMod (q ^ 2 * M'))ˣ) (x : ModularCurve.FullLevel.jacComp q M')
          (φ : Module.Dual ℂ (CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2)),
        u x = Submodule.Quotient.mk φ →
        u (ModularCurve.diamondHBar (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') d x) =
          Submodule.Quotient.mk ((CuspForm.diamondLinH 2 d).dualMap φ)) ∧
      ∃ ζ₀ : ModularCurve.FullLevel.Idx q,
        ∀ (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M')
          (τ : ModularCurve.FullLevel.fieldBar q M' ≃ₐ[AlgebraicClosure ℚ] ModularCurve.FullLevel.fieldBar q M'),
          ModularCurve.FullLevel.IsLevelAutBar q M' ζ₀ γ τ →
          ∀ (x : ModularCurve.FullLevel.jacComp q M')
            (φ : Module.Dual ℂ (CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2)),
            u x = Submodule.Quotient.mk φ →
            u (AlgebraicCurve.SemilinearAut.ofAlgAut τ • x) = Submodule.Quotient.mk ((L γ hγ).dualMap φ) := by sorry
