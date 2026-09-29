-- Prove2me | Theorems.Thm_ModularCurve_exists_heckeEquivariant_linearEquiv_tateModule_jH_padicInt_tensor_periodLatticeOf_charInvolution
-- name    : ModularCurve.exists_heckeEquivariant_linearEquiv_tateModule_jH_padicInt_tensor_periodLatticeOf_charInvolution
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/d350c9e2-68da-53d5-9c7f-1855f4e79994
-- title:
--   Tate module of J_H(M) versus the period lattice
-- statement:
--   Let $M\ge 1$ and let $p$ be a prime, let $H\le(\mathbb Z/M)^\times$ be a subgroup and $S$ an arbitrary set of natural numbers, and assume [`ModularCurve.HeckeDiamondInputsHAll M H`](def/ModularCurve_XHOperators.html#L113): for every prime $\ell$ the Hecke inputs `HeckeInputsHAlong` hold for $M,H,\ell$ over $\overline{\mathbb Q}$, and for every $d\in(\mathbb Z/M)^\times$ some $\overline{\mathbb Q}$-automorphism $\sigma$ of the function field `xHFunctionFieldBar M H` satisfies `IsDiamondAutHBar M H d σ`. Then there is an isomorphism $e$ of $\mathbb Z_p$-modules from the Tate module of $J_H(M)=\mathrm{Pic}^0$ of that function field — sequences $(x_n)$ with $p^n x_n=0$ and $p\,x_{n+1}=x_n$ — onto $\mathbb Z_p\otimes_{\mathbb Z}\Lambda$, where $\Lambda=$ `periodLatticeOf` $(\Gamma_H(M))$ is the $\mathbb Z$-span of the periods $\mathrm{periodOf}\,\delta$ inside the complex dual of $\mathrm{CuspForm}(\Gamma_H(M),2)$, with the following two adjointness properties. First, for each generator symbol $g$ in `Gen M S` ($T_\ell$ for a prime $\ell\notin S$ with $\ell\nmid M$, $U_q$ for a prime $q\mid M$, or $\langle d\rangle$ for $d\in(\mathbb Z/M)^\times$), each parabolic homomorphism $\psi:\mathrm{Additive}\,\Gamma_H(M)\to\mathbb Z_p$, and all $\mathbb Z$-linear $\chi,\chi':\Lambda\to\mathbb Z_p$ with $\chi(\mathrm{periodOf}\,\delta)=\psi(\delta)$ and $\chi'(\mathrm{periodOf}\,\delta)=(\mathrm{opFamily}\,g\,\psi)(\delta)$ for all $\delta\in\Gamma_H(M)$ (where `opFamily` sends $T_\ell,U_q$ to `heckeTL` and $\langle d\rangle$ to `diamondL` on $\mathrm{Hom}(\mathrm{Additive}\,\Gamma_H(M),\mathbb Z_p)$), the base-changed functionals satisfy $\chi'(e(x))=\chi(e(\mathrm{tateGenOpH}\,g\,x))$ for all $x$ in the Tate module. Second, the same identity holds with `charInvolution` (precomposition of $\psi$ with the conjugation automorphism `jConjGammaH` of $\Gamma_H(M)$) in place of $\mathrm{opFamily}\,g$ and with the action of [`complexConjugation`](def/GaloisRep_ComplexConjugation.html#L30) through `JH.tateGaloisRep` in place of $\mathrm{tateGenOpH}\,g$.
--
--   This is the Betti–étale comparison for the Jacobian $J_H(M)$: the $p$-adic Tate module is identified with $\mathbb Z_p$ tensored with the period lattice of weight-two cusp forms on $\Gamma_H(M)$, in such a way that the covariant Hecke and diamond operators on the Tate module correspond to the transposes of the operators on parabolic homomorphisms, and the arithmetic action of complex conjugation to the involution induced by $\gamma\mapsto$ `jConjGammaH` $\gamma$. It feeds the construction of the Hecke-equivariant map from parabolic homomorphisms to the dual of the Tate module used in the Galois-representation side of the modularity argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_heckeEquivariant_linearEquiv_tateModule_jH_padicInt_tensor_periodLatticeOf_charInvolution.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_CohCarrier_CharInvolution
import Definitions.Def_GaloisRep_ComplexConjugation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups TensorProduct

theorem ModularCurve.exists_heckeEquivariant_linearEquiv_tateModule_jH_padicInt_tensor_periodLatticeOf_charInvolution
    (M p : ℕ) [NeZero M] [Fact p.Prime] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
    (hin : ModularCurve.HeckeDiamondInputsHAll M H) :
    ∃ e : TateModule p (ModularCurve.JH M H) ≃ₗ[ℤ_[p]]
        ℤ_[p] ⊗[ℤ] ModularCurve.periodLatticeOf (CohCarrier.GammaH M H),
      (∀ (g : CohCarrier.Gen M S) (ψ : CohCarrier.H1 M H ℤ_[p]),
        ψ ∈ ModularCurve.Period.parabolicHoms ℤ_[p] (CohCarrier.GammaH M H) ℤ_[p] →
        ∀ (χ χ' : ModularCurve.periodLatticeOf (CohCarrier.GammaH M H) →ₗ[ℤ] ℤ_[p]),
          (∀ δ : CohCarrier.GammaH M H,
            χ ⟨ModularCurve.periodOf (CohCarrier.GammaH M H) δ,
              ModularCurve.periodOf_mem_periodLatticeOf (CohCarrier.GammaH M H) δ⟩ =
              ψ (Additive.ofMul δ)) →
          (∀ δ : CohCarrier.GammaH M H,
            χ' ⟨ModularCurve.periodOf (CohCarrier.GammaH M H) δ,
              ModularCurve.periodOf_mem_periodLatticeOf (CohCarrier.GammaH M H) δ⟩ =
              CohCarrier.opFamily M H S ℤ_[p] g ψ (Additive.ofMul δ)) →
          ∀ x : TateModule p (ModularCurve.JH M H),
            χ'.liftBaseChange ℤ_[p] (e x) =
              χ.liftBaseChange ℤ_[p] (e (ModularCurve.tateGenOpH M H S p g x))) ∧
      (∀ (ψ : CohCarrier.H1 M H ℤ_[p]),
        ψ ∈ ModularCurve.Period.parabolicHoms ℤ_[p] (CohCarrier.GammaH M H) ℤ_[p] →
        ∀ (χ χ' : ModularCurve.periodLatticeOf (CohCarrier.GammaH M H) →ₗ[ℤ] ℤ_[p]),
          (∀ δ : CohCarrier.GammaH M H,
            χ ⟨ModularCurve.periodOf (CohCarrier.GammaH M H) δ,
              ModularCurve.periodOf_mem_periodLatticeOf (CohCarrier.GammaH M H) δ⟩ =
              ψ (Additive.ofMul δ)) →
          (∀ δ : CohCarrier.GammaH M H,
            χ' ⟨ModularCurve.periodOf (CohCarrier.GammaH M H) δ,
              ModularCurve.periodOf_mem_periodLatticeOf (CohCarrier.GammaH M H) δ⟩ =
              CohCarrier.charInvolution M H ℤ_[p] ℤ_[p] ψ (Additive.ofMul δ)) →
          ∀ x : TateModule p (ModularCurve.JH M H),
            χ'.liftBaseChange ℤ_[p] (e x) =
              χ.liftBaseChange ℤ_[p]
                (e (ModularCurve.JH.tateGaloisRep M H p complexConjugation x))) := by sorry
