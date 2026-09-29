-- Prove2me | Theorems.Thm_ModularCurve_exists_equivariant_torsion_reduction_ofJ_evalAt_fullKernelQuotient_j_ord_mul_natCard
-- name    : ModularCurve.exists_equivariant_torsion_reduction_ofJ_evalAt_fullKernelQuotient_j_ord_mul_natCard
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/9650a086-6b29-5aed-8cb9-570819f7c31f
-- title:
--   Equivariant torsion reduction: j of the Vélu quotient and ramification
-- statement:
--   Let $K$ be an algebraically closed field of characteristic $p$, let $N\ge 1$ be an integer with $N\ne 0$ in $K$, let $j_0\in K$, and let $E_0$ be a Weierstrass curve over $K$ with invertible discriminant and $j(E_0)=j_0$. Then there exist: a field $M$ with a $K$-algebra structure; an element $t\in M$ transcendental over $K$ such that $M$ is finite and Galois over $K\langle t\rangle$; a place $W_0$ of $M$ over $K$, that is a valuation subring of $M$ containing the image of $K$, different from $M$ and a principal ideal ring, with $\operatorname{ord}_{W_0}(t-j_0)>0$ (where $\operatorname{ord}$ is minus the logarithm of the associated adic valuation); an additive map $\theta$ from the affine points of $E_M$, the base change to $M$ of the curve $\mathrm{ofJ}(t)$ over $K\langle t\rangle$, to the affine points of $E_0$; and a map $\rho$ from $\mathrm{Gal}(M/K\langle t\rangle)$ to the group of Weierstrass variable changes over $K$, subject to the following. The group of $P$ with $N\cdot P=0$ in $E_M$ has exactly $N^2$ elements. If $n$ is prime to $p$, $n\cdot P=0$ and $\theta P=0$, then $P=0$. Writing $D$ for the set of $\sigma\in\mathrm{Gal}(M/K\langle t\rangle)$ whose associated semilinear automorphism (the pair $(\sigma,\mathrm{id}_K)$) fixes $W_0$: for $\sigma\in D$ one has $\rho\sigma\cdot E_0=E_0$; $\rho$ is multiplicative on $D$; for $\sigma\in D$ and all $P$, the inverse variable-change transport $\mathrm{vcInvFun}(\rho\sigma)(\theta P)$ agrees (as a heterogeneous equality, the two point types differing by the variable change) with $\theta(\sigma P)$; every variable change $\gamma$ with $\gamma\cdot E_0=E_0$ is realised in this way by some $\sigma\in D$, up to a global sign; and $\sigma\in D$ with $\rho\sigma=1$ is trivial. Finally, let $Q$ be a point of $E_M$ of exact order $N$, and form the full-kernel Vélu quotients of $E_M$ by $Q$ and of $E_0$ by $\theta Q$ (same $a_1,a_2,a_3$, with $a_4$ and $a_6$ corrected by the Vélu sums $\sum g_x$ and $\sum(xg_x-yg_y)$ over the coordinates of $k\cdot Q$ for $1\le k\le N-1$), and assume both have nonzero discriminant. Then $j(E_M/\langle Q\rangle)$ lies in the valuation ring of $W_0$ and its residue, pulled back to $K$, equals $j(E_0/\langle\theta Q\rangle)$; and $$\operatorname{ord}_{W_0}\bigl(j(E_M/\langle Q\rangle)-j(E_0/\langle\theta Q\rangle)\bigr)\cdot\#\mathrm{Stab}(E_0)=\operatorname{ord}_{W_0}(t-j_0)\cdot\#\mathrm{Stab}\bigl(E_0/\langle\theta Q\rangle\bigr),$$ the stabilisers being taken for the action of variable changes over $K$ on Weierstrass curves.
--
--   This packages the generic elliptic curve $\mathrm{ofJ}(t)$ together with a place specialising $t$ to $j_0$, a reduction map $\theta$ onto $E_0$ equivariant for the decomposition group, and the comparison of $j$-invariants of the $N$-isogenous quotients; the final identity is the ramification statement for $X_0(N)\to X(1)$ at the point in question, expressed through the orders of the automorphism groups of $E_0$ and of $E_0/\langle\theta Q\rangle$. It is used in the construction of the modular orbit map on cyclic subgroups of order $N$ with its second coordinate, in [`ModularCurve.exists_orbitMap_cyclicAddSubgroup_places_evalAt_jqNModC_eq_and_ord_sub_eq_natCard`](thm.html#ModularCurve.exists_orbitMap_cyclicAddSubgroup_places_evalAt_jqNModC_eq_and_ord_sub_eq_natCard).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_equivariant_torsion_reduction_ofJ_evalAt_fullKernelQuotient_j_ord_mul_natCard.lean

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_WeierstrassCurve_FullKernelQuotient
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve WeierstrassCurve WeierstrassCurve.Affine
open scoped IntermediateField
universe u in

theorem ModularCurve.exists_equivariant_torsion_reduction_ofJ_evalAt_fullKernelQuotient_j_ord_mul_natCard
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
          ρ σ = 1 → σ = 1) ∧

      (∀ (Q : ((WeierstrassCurve.ofJ
          (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point),
          addOrderOf Q = N →
          ∀ (hΔ : (((WeierstrassCurve.ofJ
              (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).fullKernelQuotient Q N).Δ ≠ 0)
            (hΔ₀ : (E₀.fullKernelQuotient (θ Q) N).Δ ≠ 0),
            @WeierstrassCurve.j M _ (((WeierstrassCurve.ofJ
                (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).fullKernelQuotient Q N)
              ⟨isUnit_iff_ne_zero.mpr hΔ⟩ ∈ W₀.toValuationSubring ∧
            W₀.evalAt (@WeierstrassCurve.j M _ (((WeierstrassCurve.ofJ
                (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).fullKernelQuotient Q N)
              ⟨isUnit_iff_ne_zero.mpr hΔ⟩) =
              @WeierstrassCurve.j K _ (E₀.fullKernelQuotient (θ Q) N) ⟨isUnit_iff_ne_zero.mpr hΔ₀⟩) ∧

      (∀ (Q : ((WeierstrassCurve.ofJ
          (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point),
          addOrderOf Q = N →
          ∀ (hΔ : (((WeierstrassCurve.ofJ
              (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).fullKernelQuotient Q N).Δ ≠ 0)
            (hΔ₀ : (E₀.fullKernelQuotient (θ Q) N).Δ ≠ 0),
            W₀.ord (@WeierstrassCurve.j M _ (((WeierstrassCurve.ofJ
                (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).fullKernelQuotient Q N)
              ⟨isUnit_iff_ne_zero.mpr hΔ⟩ -
                algebraMap K M (@WeierstrassCurve.j K _ (E₀.fullKernelQuotient (θ Q) N) ⟨isUnit_iff_ne_zero.mpr hΔ₀⟩))
              * (Nat.card (MulAction.stabilizer (WeierstrassCurve.VariableChange K) E₀) : ℤ) =
            W₀.ord (t - algebraMap K M j₀)
              * (Nat.card (MulAction.stabilizer (WeierstrassCurve.VariableChange K)
                  (E₀.fullKernelQuotient (θ Q) N)) : ℤ)) := by sorry
