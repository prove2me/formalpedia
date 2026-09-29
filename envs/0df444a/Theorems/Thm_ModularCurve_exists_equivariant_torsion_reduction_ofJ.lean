-- Prove2me | Theorems.Thm_ModularCurve_exists_equivariant_torsion_reduction_ofJ
-- name    : ModularCurve.exists_equivariant_torsion_reduction_ofJ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/e5d67976-e679-56a7-91f0-eb223dcc5b20
-- title:
--   Equivariant reduction of ofJ(t) at a place over j₀
-- statement:
--   Let $K$ be an algebraically closed field of characteristic $p$, let $N\ge 1$ be an integer with $N\ne 0$ in $K$, let $j_0\in K$, and let $E_0$ be a Weierstrass curve over $K$ which is elliptic and has $j$-invariant $j_0$. The assertion is the existence of: a field $M$ with a $K$-algebra structure; an element $t\in M$ transcendental over $K$ such that $M$ is finite-dimensional and Galois over $K\langle t\rangle$; a place $W_0$ of $M$ over $K$ in the sense of the project, that is, a valuation subring of $M$ containing $\operatorname{im}(K\to M)$, not equal to $M$, whose ring is a principal ideal ring, with $\operatorname{ord}_{W_0}(t-j_0)>0$ (the order being minus the logarithm of the associated adic valuation); an additive homomorphism $\theta$ from the group of affine points of the base change to $M$ of `WeierstrassCurve.ofJ` applied to $t\in K\langle t\rangle$ — write $E$ for that curve — to the affine points of $E_0$; and a function $\rho$ from $\mathrm{Gal}(M/K\langle t\rangle)$ to the group of variable changes over $K$, subject to seven conditions. First, $\{P\in E(M): N\cdot P=0\}$ has exactly $N^2$ elements. Second, $\theta$ kills no nonzero point of order prime to $p$: if $p\nmid n$, $n\cdot P=0$ and $\theta P=0$, then $P=0$. The remaining four conditions concern those $\sigma$ whose associated semilinear automorphism $(\sigma,\mathrm{id}_K)$ fixes $W_0$ (the decomposition group of $W_0$): for such $\sigma$, $\rho\sigma\cdot E_0=E_0$; $\rho$ is multiplicative on this set; for every point $P$ of $E(M)$ the point $\mathrm{vcInvFun}(\rho\sigma)$ applied to $\theta P$ agrees (as a heterogeneous equality, the target type being that of $(\rho\sigma)\cdot E_0=E_0$) with $\theta$ of the image of $P$ under $\sigma$; conversely, every variable change $\gamma$ over $K$ with $\gamma\cdot E_0=E_0$ is realised up to sign by some $\sigma$ in the decomposition group, in the sense that $\mathrm{vcInvFun}(\gamma)\circ\theta$ equals either $\theta\circ\sigma$ or $-(\theta\circ\sigma)$ on all points; and finally $\rho$ is injective on the decomposition group at the identity: $\rho\sigma=1$ forces $\sigma=1$.
--
--   This packages, in the form required later, Deuring's description of the reduction of the generic elliptic curve with $j$-invariant $t$ at a place specialising $t$ to $j_0$: over a field $M$ trivialising enough torsion the curve acquires good reduction with reduced model $E_0$, the reduction map on prime-to-$p$ torsion is injective, and the decomposition group acts through the automorphisms of $E_0$ faithfully and (up to sign) surjectively. It is used in the construction of places and level structures on modular curves, notably in the results on $\Gamma_H$-function fields in characteristics $2$ and $3$ and in the double-coset statement about diamond operators fixing a place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_equivariant_torsion_reduction_ofJ.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve WeierstrassCurve WeierstrassCurve.Affine
open scoped IntermediateField

universe u in

theorem ModularCurve.exists_equivariant_torsion_reduction_ofJ
    (K : Type u) [Field K] [IsAlgClosed K] [DecidableEq K] (p : ℕ) [CharP K p]
    (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) (j₀ : K)
    (E₀ : WeierstrassCurve K) [E₀.IsElliptic] (hE₀ : E₀.j = j₀) :
    ∃ (M : Type u) (_ : Field M) (_ : DecidableEq M) (_ : Algebra K M) (t : M)
      (_ : Transcendental K t) (_ : FiniteDimensional K⟮t⟯ M) (_ : IsGalois K⟮t⟯ M)
      (W₀ : Place K M) (_ : 0 < W₀.ord (t - algebraMap K M j₀))
      (θ : ((WeierstrassCurve.ofJ
            (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point
          →+ E₀.toAffine.Point)
      (ρ : (M ≃ₐ[K⟮t⟯] M) → VariableChange K),
      Nat.card {P : ((WeierstrassCurve.ofJ
        (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point //
          N • P = 0} = N ^ 2 ∧
      (∀ (n : ℕ) (P : ((WeierstrassCurve.ofJ
          (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point),
          ¬ p ∣ n → n • P = 0 → θ P = 0 → P = 0) ∧
      (∀ σ : M ≃ₐ[K⟮t⟯] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ →
          ρ σ • E₀ = E₀) ∧
      (∀ σ τ : M ≃ₐ[K⟮t⟯] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ →
          SemilinearAut.ofAlgAut (τ.restrictScalars K) • W₀ = W₀ → ρ (σ * τ) = ρ σ * ρ τ) ∧
      (∀ σ : M ≃ₐ[K⟮t⟯] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ →
          ∀ P, HEq (Point.vcInvFun (ρ σ) E₀.toAffine (θ P))
            (θ (WeierstrassCurve.Affine.Point.map (σ : M →ₐ[K⟮t⟯] M) P))) ∧
      (∀ γ : VariableChange K, γ • E₀ = E₀ →
          ∃ σ : M ≃ₐ[K⟮t⟯] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ ∧
            ((∀ P, HEq (Point.vcInvFun γ E₀.toAffine (θ P))
                (θ (WeierstrassCurve.Affine.Point.map (σ : M →ₐ[K⟮t⟯] M) P))) ∨
             (∀ P, HEq (Point.vcInvFun γ E₀.toAffine (θ P))
                (-θ (WeierstrassCurve.Affine.Point.map (σ : M →ₐ[K⟮t⟯] M) P))))) ∧
      (∀ σ : M ≃ₐ[K⟮t⟯] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ →
          ρ σ = 1 → σ = 1) := by sorry
