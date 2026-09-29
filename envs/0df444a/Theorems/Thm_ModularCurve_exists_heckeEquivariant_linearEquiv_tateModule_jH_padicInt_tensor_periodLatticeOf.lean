-- Prove2me | Theorems.Thm_ModularCurve_exists_heckeEquivariant_linearEquiv_tateModule_jH_padicInt_tensor_periodLatticeOf
-- name    : ModularCurve.exists_heckeEquivariant_linearEquiv_tateModule_jH_padicInt_tensor_periodLatticeOf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/fb2503b0-0935-5e65-8fe1-b10426d9bf42
-- title:
--   Hecke-equivariant comparison Tₚ J_H(M) ≅ ℤₚ ⊗ Λ_{Γ_H(M)}
-- statement:
--   Let $M \ge 1$ and let $p$ be a prime, let $H \le (\mathbb{Z}/M)^\times$ be a subgroup and $S \subseteq \mathbb{N}$ a set of primes to be excluded, and write $\Gamma = \Gamma_H(M)$ for the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ obtained as the image in $\mathrm{SL}_2(\mathbb{Z})$ of the preimage of $H$ under the character $\Gamma_0(M) \to (\mathbb{Z}/M)^\times$ given by the lower-right entry. Assume [`ModularCurve.HeckeDiamondInputsHAll M H`](def/ModularCurve_XHOperators.html#L113), that is: for every prime $\ell$ the Hecke data `HeckeInputsHAlong` over $\overline{\mathbb{Q}}$ at level $(M,H)$ and index $\ell$ hold, and for every $d \in (\mathbb{Z}/M)^\times$ there is a $\overline{\mathbb{Q}}$-automorphism $\sigma$ of the geometric function field `xHFunctionFieldBar M H` satisfying `IsDiamondAutHBar M H d σ`. Then there exists a $\mathbb{Z}_p$-linear isomorphism $e$ from the Tate module $T_p J_H(M)$ — the group of sequences $(x_n)_{n \in \mathbb{N}}$ in the degree-zero divisor class group $J_H(M) = \mathrm{Pic}^0$ of `xHFunctionFieldBar M H` over $\overline{\mathbb{Q}}$ with $p^n x_n = 0$ and $p\, x_{n+1} = x_n$ — onto $\mathbb{Z}_p \otimes_{\mathbb{Z}} \Lambda_\Gamma$, where $\Lambda_\Gamma =$ [`ModularCurve.periodLatticeOf`](def/ModularCurve_PeriodOf.html#L65) $\Gamma$ is the $\mathbb{Z}$-span inside the complex dual of $S_2(\Gamma) =$ `CuspForm` $\Gamma$ $2$ of the periods `periodOf` $\Gamma\, \delta$, $\delta \in \Gamma$, with the following equivariance. For every formal Hecke symbol $g \in$ [`CohCarrier.Gen M S`](def/CohCarrier_Inst.html#L13) (a $T_\ell$ for a prime $\ell \notin S$ with $\ell \nmid M$, a $U_q$ for a prime $q \mid M$, or a diamond $\langle d\rangle$ for $d \in (\mathbb{Z}/M)^\times$), every additive homomorphism $\psi : \mathrm{Additive}\,\Gamma \to \mathbb{Z}_p$ lying in [`ModularCurve.Period.parabolicHoms`](def/ModularCurve_PeriodMap.html#L62) (i.e. satisfying `IsParabolicHom`), and every pair of $\mathbb{Z}$-linear maps $\chi, \chi' : \Lambda_\Gamma \to \mathbb{Z}_p$ such that $\chi$ sends the period of $\delta$ to $\psi(\delta)$ for all $\delta \in \Gamma$ and $\chi'$ sends the period of $\delta$ to $\bigl(\mathrm{opFamily}\,g\,\psi\bigr)(\delta)$ for all $\delta \in \Gamma$, where [`CohCarrier.opFamily M H S ℤ_[p]`](def/CohCarrier_Inst.html#L91) assigns to $T_\ell$ and $U_q$ the operator `heckeTL` (precomposition with `conjL` followed by corestriction) and to $\langle d\rangle$ the operator `diamondL` on $H^1(\Gamma, \mathbb{Z}_p) = \mathrm{Hom}(\mathrm{Additive}\,\Gamma, \mathbb{Z}_p)$, one has, for all $x \in T_p J_H(M)$, $$\chi'^{\,\mathbb{Z}_p}(e(x)) = \chi^{\,\mathbb{Z}_p}\bigl(e(\mathrm{tateGenOpH}\,g\,(x))\bigr),$$ the superscript denoting base change of $\chi, \chi'$ to $\mathbb{Z}_p \otimes_{\mathbb{Z}} \Lambda_\Gamma$ and [`ModularCurve.tateGenOpH M H S p g`](def/ModularCurve_XHOperators.html#L99) the $\mathbb{Z}_p$-endomorphism of the Tate module induced by the geometric operator `genOpH` attached to $g$.
--
--   This is the integral Betti–étale comparison for the Jacobian of $X_H(M)$: the $p$-adic Tate module of $J_H(M)$ is identified with $\mathbb{Z}_p \otimes_{\mathbb{Z}} H_1$, realised as the period lattice $\Lambda_{\Gamma_H(M)}$ in the dual of the space of weight-two cusp forms, compatibly with the Hecke correspondences and diamond operators, the transposed (covariant) form of their action on parabolic cohomology being expressed through the functionals $\chi, \chi'$. It feeds the construction of the $p$-adic Galois representation attached to weight-two forms on $\Gamma_H(M)$ and the comparison of characteristic polynomials of Hecke operators with those of the Tate-module action, including the Eichler–Shimura relation at good primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_heckeEquivariant_linearEquiv_tateModule_jH_padicInt_tensor_periodLatticeOf.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_PeriodOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups TensorProduct

theorem ModularCurve.exists_heckeEquivariant_linearEquiv_tateModule_jH_padicInt_tensor_periodLatticeOf
    (M p : ℕ) [NeZero M] [Fact p.Prime] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
    (hin : ModularCurve.HeckeDiamondInputsHAll M H) :
    ∃ e : TateModule p (ModularCurve.JH M H) ≃ₗ[ℤ_[p]]
        ℤ_[p] ⊗[ℤ] ModularCurve.periodLatticeOf (CohCarrier.GammaH M H),
      ∀ (g : CohCarrier.Gen M S) (ψ : CohCarrier.H1 M H ℤ_[p]),
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
              χ.liftBaseChange ℤ_[p] (e (ModularCurve.tateGenOpH M H S p g x)) := by sorry
