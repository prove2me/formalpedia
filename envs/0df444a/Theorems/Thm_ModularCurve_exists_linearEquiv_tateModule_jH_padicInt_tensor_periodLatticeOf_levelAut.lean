-- Prove2me | Theorems.Thm_ModularCurve_exists_linearEquiv_tateModule_jH_padicInt_tensor_periodLatticeOf_levelAut
-- name    : ModularCurve.exists_linearEquiv_tateModule_jH_padicInt_tensor_periodLatticeOf_levelAut
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/54c330c3-a41a-5040-92a3-03a110a35c3c
-- title:
--   Tate module of J_H(q²M') versus period lattice, with level automorphisms
-- statement:
--   Let $q$ and $p$ be primes, $M'\ge 1$, put $M=q^2M'$ and let $H=\mathrm{levelH}\,q\,M'$ be the kernel of the reduction $(\mathbb Z/M)^\times\to(\mathbb Z/q)^\times$, so that $\Gamma=\mathrm{GammaH}\,M\,H\le \mathrm{SL}_2(\mathbb Z)$ is the corresponding congruence subgroup; let $S\subseteq\mathbb N$. Assume `HeckeDiamondInputsHAll` for $(M,H)$: the Hecke inputs `HeckeInputsHAlong` over $\overline{\mathbb Q}$ hold for every prime $\ell$, and every $d\in(\mathbb Z/M)^\times$ is realised by an automorphism of $\overline{\mathbb Q}\cdot(\text{function field of }X_H)$ satisfying `IsDiamondAutHBar`. Assume given, for each $\gamma\in\Gamma_0(M')$, a $\mathbb C$-linear endomorphism $L_\gamma$ of $S_2(\Gamma)$ with $L_\gamma f=f\mid_2(\gamma^{\sharp})^{-1}$, where $\gamma^\sharp=\mathrm{conjElem}\,q\,\gamma$ is the matrix $\begin{pmatrix}a&b/q\\ qc&d\end{pmatrix}\in\mathrm{GL}_2(\mathbb R)$ attached to $\gamma=\begin{pmatrix}a&b\\ c&d\end{pmatrix}$, and such that the dual map of $L_\gamma$ preserves the period lattice $\Lambda=\mathrm{periodLatticeOf}\,\Gamma$, the $\mathbb Z$-span inside $\mathrm{Dual}_{\mathbb C}S_2(\Gamma)$ of the periods $\mathrm{periodOf}\,\Gamma\,\delta$. Then there is a $\mathbb Z_p$-linear isomorphism $e\colon T_p(J_H(M))\xrightarrow{\sim}\mathbb Z_p\otimes_{\mathbb Z}\Lambda$, where $T_p$ denotes the module of sequences $(x_n)$ in $J_H(M)$ with $p^nx_n=0$ and $px_{n+1}=x_n$, with the following two properties. First, for every generator $g$ of $\mathrm{Gen}\,M\,S$ (a symbol $T_\ell$ for a prime $\ell\notin S$ with $\ell\nmid M$, $U_{q'}$ for a prime $q'\mid M$, or $\langle d\rangle$ for $d\in(\mathbb Z/M)^\times$), every parabolic homomorphism $\psi\colon\mathrm{Additive}\,\Gamma\to\mathbb Z_p$ (one vanishing on all $\delta$ with $\mathrm{tr}(\delta)^2=4$) and all $\mathbb Z$-linear $\chi,\chi'\colon\Lambda\to\mathbb Z_p$ with $\chi(\mathrm{periodOf}\,\Gamma\,\delta)=\psi(\delta)$ and $\chi'(\mathrm{periodOf}\,\Gamma\,\delta)=(\mathrm{opFamily}\,M\,H\,S\,\mathbb Z_p\,g\,\psi)(\delta)$ for all $\delta\in\Gamma$, one has $\chi'_{\mathbb Z_p}(e\,x)=\chi_{\mathbb Z_p}(e(\mathrm{tateGenOpH}\,M\,H\,S\,p\,g\,x))$ for all $x\in T_p(J_H(M))$, where subscript $\mathbb Z_p$ denotes base change to $\mathbb Z_p$ and $\mathrm{tateGenOpH}$ is the endomorphism of the Tate module induced by the correspondence or diamond automorphism $\mathrm{genOpH}$ attached to $g$. Secondly, there is a primitive $q$-th root of unity $\zeta_0\in\overline{\mathbb Q}$ such that for every $\gamma\in\Gamma_0(M')$, every monoid endomorphism $c$ of $\Gamma$ with $c\,\delta=(\gamma^\sharp)^{-1}\delta\,\gamma^\sharp$ in $\mathrm{GL}_2(\mathbb R)$ for all $\delta$, every automorphism $\tau$ of $\mathrm{fieldBar}\,q\,M'$ over $\overline{\mathbb Q}$ satisfying $\mathrm{IsLevelAutBar}\,q\,M'\,\zeta_0\,\gamma\,\tau$, and all $\mathbb Z$-linear $\chi,\chi'\colon\Lambda\to\mathbb Z_p$ with $\chi'(\mathrm{periodOf}\,\Gamma\,\delta)=\chi(\mathrm{periodOf}\,\Gamma\,(c\,\delta))$ for all $\delta\in\Gamma$, one has $\chi'_{\mathbb Z_p}(e\,x)=\chi_{\mathbb Z_p}(e(T_p(A_\tau)\,x))$ for all $x$, where $A_\tau$ is the additive endomorphism of $J_H(M)$ obtained from the semilinear automorphism $\mathrm{ofAlgAut}\,\tau$ and $T_p(A_\tau)$ its action on the Tate module.
--
--   This is the Betti–étale comparison for the Jacobian of $X_H(q^2M')$ in the form used for the full-level construction: the $p$-adic Tate module is identified with $\mathbb Z_p\otimes\Lambda$ compatibly with the Hecke and diamond operators (tested against parabolic $\mathbb Z_p$-valued homomorphisms on $\Gamma$) and, in addition, with the automorphisms of the geometric function field attached to elements of $\Gamma_0(M')$ via the conjugating matrices $\gamma^\sharp$. It is cited by [`ModularCurve.FullLevel.exists_injective_cuspForm_dual_baseChange_tateModule_jacComp_comm`](thm.html#ModularCurve.FullLevel.exists_injective_cuspForm_dual_baseChange_tateModule_jacComp_comm).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_linearEquiv_tateModule_jH_padicInt_tensor_periodLatticeOf_levelAut.lean

import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped MatrixGroups ModularForm TensorProduct

theorem ModularCurve.exists_linearEquiv_tateModule_jH_padicInt_tensor_periodLatticeOf_levelAut
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (S : Set ℕ) (p : ℕ) [Fact p.Prime]
    (hin : ModularCurve.HeckeDiamondInputsHAll (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))
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
    ∃ e : TateModule p (ModularCurve.FullLevel.jacComp q M') ≃ₗ[ℤ_[p]]
        ℤ_[p] ⊗[ℤ] ModularCurve.periodLatticeOf (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')),
      (∀ (g : CohCarrier.Gen (q ^ 2 * M') S)
          (ψ : CohCarrier.H1 (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') ℤ_[p]),
        ψ ∈ ModularCurve.Period.parabolicHoms ℤ_[p]
            (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) ℤ_[p] →
        ∀ (χ χ' : ModularCurve.periodLatticeOf
              (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) →ₗ[ℤ] ℤ_[p]),
          (∀ δ : CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'),
            χ ⟨ModularCurve.periodOf _ δ, ModularCurve.periodOf_mem_periodLatticeOf _ δ⟩ = ψ (Additive.ofMul δ)) →
          (∀ δ : CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'),
            χ' ⟨ModularCurve.periodOf _ δ, ModularCurve.periodOf_mem_periodLatticeOf _ δ⟩ =
              CohCarrier.opFamily (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') S ℤ_[p] g ψ
                (Additive.ofMul δ)) →
          ∀ x : TateModule p (ModularCurve.FullLevel.jacComp q M'),
            χ'.liftBaseChange ℤ_[p] (e x) =
              χ.liftBaseChange ℤ_[p]
                (e (ModularCurve.tateGenOpH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') S p g x))) ∧
      ∃ ζ₀ : ModularCurve.FullLevel.Idx q,
        ∀ (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M')
          (c : ↥(CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) →*
            ↥(CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))),
          (∀ δ : ↥(CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')),
            (((c δ : ↥(CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))) : SL(2, ℤ)) :
                GL (Fin 2) ℝ) =
              (ModularCurve.FullLevel.conjElem q γ)⁻¹ * ((δ : SL(2, ℤ)) : GL (Fin 2) ℝ) *
                ModularCurve.FullLevel.conjElem q γ) →
          ∀ (τ : ModularCurve.FullLevel.fieldBar q M' ≃ₐ[AlgebraicClosure ℚ] ModularCurve.FullLevel.fieldBar q M'),
            ModularCurve.FullLevel.IsLevelAutBar q M' ζ₀ γ τ →
            ∀ (χ χ' : ModularCurve.periodLatticeOf
                (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) →ₗ[ℤ] ℤ_[p]),
              (∀ δ : CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'),
                χ' ⟨ModularCurve.periodOf _ δ, ModularCurve.periodOf_mem_periodLatticeOf _ δ⟩ =
                  χ ⟨ModularCurve.periodOf _ (c δ), ModularCurve.periodOf_mem_periodLatticeOf _ (c δ)⟩) →
              ∀ x : TateModule p (ModularCurve.FullLevel.jacComp q M'),
                χ'.liftBaseChange ℤ_[p] (e x) =
                  χ.liftBaseChange ℤ_[p]
                    (e (TateModule.rep p (ModularCurve.FullLevel.jacComp q M')
                      (AddMonoid.End (ModularCurve.FullLevel.jacComp q M'))
                      (DistribSMul.toAddMonoidHom (ModularCurve.FullLevel.jacComp q M')
                        (AlgebraicCurve.SemilinearAut.ofAlgAut τ)) x)) := by sorry
