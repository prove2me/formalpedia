-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_injective_cuspForm_dual_baseChange_tateModule_jacComp_comm
-- name    : ModularCurve.FullLevel.exists_injective_cuspForm_dual_baseChange_tateModule_jacComp_comm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/08980ae3-fc9e-515a-b241-2a846123aad3
-- title:
--   Cusp forms embed in the dual complexified Tate module of J_H
-- statement:
--   Let $q$ and $\lambda$ be primes, let $M'\ge 1$, and fix a $\mathbb{Z}_\lambda$-algebra structure on $\mathbb{C}$. Write $H=\mathrm{levelH}\,q\,M'$ for the kernel of the reduction $(\mathbb{Z}/q^2M')^\times\to(\mathbb{Z}/q)^\times$, $\Gamma_H\le \mathrm{SL}_2(\mathbb{Z})$ for the associated subgroup [`CohCarrier.GammaH`](def/CohCarrier_Level.html#L133) of $\Gamma_0(q^2M')$, and $J=\mathrm{jacComp}\,q\,M'=J_H(q^2M')$ over $\overline{\mathbb{Q}}$. Assume: `HeckeDiamondInputsHAll` for $(q^2M',H)$, i.e. the data `HeckeInputsHAlong` over $\overline{\mathbb{Q}}$ for every prime $\ell$ together with, for each $d\in(\mathbb{Z}/q^2M')^\times$, an automorphism of $\mathrm{xHFunctionFieldBar}$ satisfying `IsDiamondAutHBar`; `LevelAutInputs`, i.e. for every primitive $q$-th root of unity $\zeta$ in $\overline{\mathbb{Q}}$ and every $\gamma\in\Gamma_0(M')$ an $\overline{\mathbb{Q}}$-automorphism of $\mathrm{fieldBar}\,q\,M'$ satisfying `IsLevelAutBar`; and a family of $\mathbb{C}$-linear endomorphisms $L_\gamma$ of $S_2(\Gamma_H)$, indexed by $\gamma\in\Gamma_0(M')$, with $L_\gamma f=f\mid_2(\gamma^\sharp)^{-1}$, where $\gamma^\sharp=\mathrm{conjElem}\,q\,\gamma$ is the real matrix $\begin{pmatrix}a&b/q\\ qc&d\end{pmatrix}$ for $\gamma=\begin{pmatrix}a&b\\ c&d\end{pmatrix}$, and such that each dual map $L_\gamma^\vee$ preserves the period lattice $\mathrm{periodLatticeOf}\,\Gamma_H$, the $\mathbb{Z}$-span of the range of $\mathrm{periodOf}\,\Gamma_H$ in $\mathrm{Hom}_{\mathbb{C}}(S_2(\Gamma_H),\mathbb{C})$. Then there exist a primitive $q$-th root of unity $\zeta_0\in\overline{\mathbb{Q}}$ (an element of $\mathrm{Idx}\,q$) and an injective $\mathbb{C}$-linear map $$\Psi\colon S_2(\Gamma_H)\longrightarrow \mathrm{Hom}_{\mathbb{C}}\bigl(\mathbb{C}\otimes_{\mathbb{Z}_\lambda}T_\lambda J,\mathbb{C}\bigr),$$ where $T_\lambda J=\mathrm{TateModule}\,\lambda\,J$ is the group of sequences $(x_n)$ in $J$ with $\lambda^n x_n=0$ and $\lambda x_{n+1}=x_n$, with the following three compatibilities. For every prime $\ell\nmid q^2M'$ and every $F$, the $\mathbb{C}$-dual of the base change to $\mathbb{C}$ of the $\mathbb{Z}_\lambda$-linear endomorphism of $T_\lambda J$ induced through [`TateModule.rep`](def/EllipticCurve_TateModule.html#L174) by the additive endomorphism $\mathrm{heckeOperatorHAlong}\,\overline{\mathbb{Q}}\,(q^2M')\,H\,\ell$ of $J$ sends $\Psi F$ to $\Psi(\mathrm{heckeTLinH}\,2\,h_\ell\,h_{\ell M}\,F)$; for every $d\in(\mathbb{Z}/q^2M')^\times$ the same holds with $\mathrm{diamondHBar}\,(q^2M')\,H\,d$ on $J$ and $\mathrm{diamondLinH}\,2\,d$ on forms; and for every $\gamma\in\Gamma_0(M')$ with $\mathrm{levelOp}\,q\,M'\,\zeta_0\,\gamma$ on $J$ and $L_\gamma$ on forms. (Here $\mathrm{heckeTLinH}$ and $\mathrm{diamondLinH}$ are defined as the Hecke and diamond operators when the respective stability predicates `StableT`, `StableD` hold and as $0$ otherwise; these predicates hold in the present situation.)
--
--   This is the Abel–Jacobi and Betti–étale comparison step for the curve $X_H(q^2M')$ in the form needed at full level at $q$: weight-two cusp forms are embedded, Hecke-, diamond- and level-operator-equivariantly, into the dual of the complexified $\lambda$-adic Tate module of the Jacobian, the covariant operators on the Jacobian acting by transposition. It feeds [`ModularCurve.FullLevel.exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span`](thm.html#ModularCurve.FullLevel.exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span), which isolates the newform eigenspace and produces the associated $\lambda$-adic representation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_injective_cuspForm_dual_baseChange_tateModule_jacComp_comm.lean

import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Mathlib.RingTheory.TensorProduct.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped MatrixGroups ModularForm TensorProduct

theorem ModularCurve.FullLevel.exists_injective_cuspForm_dual_baseChange_tateModule_jacComp_comm
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (lam : ℕ) [Fact lam.Prime] [Algebra ℤ_[lam] ℂ]
    (hin : ModularCurve.HeckeDiamondInputsHAll (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))
    (hLA : ModularCurve.FullLevel.LevelAutInputs q M')
    (L : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      (CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2 →ₗ[ℂ] CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2))
    (hL : ∀ (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M') (f : CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2),
      ⇑(L γ hγ f) = ⇑f ∣[(2 : ℤ)] (ModularCurve.FullLevel.conjElem q γ)⁻¹)
    (hstL : ∀ (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M'),
      ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')), (L γ hγ).dualMap v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))) :
    ∃ (ζ₀ : ModularCurve.FullLevel.Idx q)
      (Ψ : CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2 →ₗ[ℂ] Module.Dual ℂ (ℂ ⊗[ℤ_[lam]] TateModule lam (ModularCurve.FullLevel.jacComp q M'))),
      Function.Injective Ψ ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ q ^ 2 * M') (F : CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2),
        ((TateModule.rep lam (ModularCurve.FullLevel.jacComp q M') (AddMonoid.End (ModularCurve.FullLevel.jacComp q M'))
            (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
              (ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) (q ^ 2 * M')
                (ModularCurve.FullLevel.levelH q M') ℓ : AddMonoid.End (ModularCurve.FullLevel.jacComp q M')))).baseChange ℂ).dualMap (Ψ F) =
          Ψ (CuspForm.heckeTLinH 2 hℓ hℓM F)) ∧
      (∀ (d : (ZMod (q ^ 2 * M'))ˣ) (F : CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2),
        ((TateModule.rep lam (ModularCurve.FullLevel.jacComp q M') (AddMonoid.End (ModularCurve.FullLevel.jacComp q M'))
            (ModularCurve.diamondHBar (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') d :
              AddMonoid.End (ModularCurve.FullLevel.jacComp q M'))).baseChange ℂ).dualMap (Ψ F) =
          Ψ (CuspForm.diamondLinH 2 d F)) ∧
      (∀ (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M') (F : CuspForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) 2),
        ((TateModule.rep lam (ModularCurve.FullLevel.jacComp q M') (AddMonoid.End (ModularCurve.FullLevel.jacComp q M'))
            (ModularCurve.FullLevel.levelOp q M' ζ₀ γ : AddMonoid.End (ModularCurve.FullLevel.jacComp q M'))).baseChange ℂ).dualMap (Ψ F) =
          Ψ (L γ hγ F)) := by sorry
