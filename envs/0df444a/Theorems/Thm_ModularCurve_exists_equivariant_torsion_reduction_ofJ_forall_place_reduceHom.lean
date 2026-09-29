-- Prove2me | Theorems.Thm_ModularCurve_exists_equivariant_torsion_reduction_ofJ_forall_place_reduceHom
-- name    : ModularCurve.exists_equivariant_torsion_reduction_ofJ_forall_place_reduceHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/3040d0ad-8c2a-5aaf-93f2-3167f6dd436d
-- title:
--   Equivariant reduction of torsion for the generic curve over the j-line
-- statement:
--   Let $K$ be an algebraically closed field with decidable equality and $\operatorname{char} K = p$, and let $N \ge 1$ be an integer with $N \ne 0$ in $K$. The assertion is the existence of a field $M$ with decidable equality, carrying a $K$-algebra structure, and of an element $t \in M$ transcendental over $K$ such that $M$ is a finite Galois extension of $K\langle t\rangle = K(t)$, with the following two properties. First, the curve $\mathrm{ofJ}(t)$ over $K(t)$ (the standard Weierstrass model of $j$-invariant $t$), base changed to $M$, has exactly $N^2$ affine points $P$ with $N \cdot P = 0$. Second, for every $j_0 \in K$, every Weierstrass curve $E_0$ over $K$ that is elliptic with $j(E_0) = j_0$, and every place $W_0$ of $M$ over $K$ — that is, a valuation subring $A \subseteq M$, not equal to $M$, containing the image of $K$ and a principal ideal ring, with decidable equality on its residue field — such that $\operatorname{ord}_{W_0}(t - j_0) > 0$, there exist: a Weierstrass curve $W_A$ over $A$; a variable change $\kappa_0$ over $M$; a ring isomorphism $e$ from the residue field of $A$ onto $K$; a variable change $\gamma_0$ over $K$; a proof $h_\Delta$ that the reduction $\widetilde{W_A} = W_A \bmod \mathfrak{m}_A$ has nonzero discriminant; an additive map $\theta$ from the $M$-points of $\mathrm{ofJ}(t)_M$ to the points of $E_0$; and a map $\rho$ from $\mathrm{Gal}(M/K(t))$ to variable changes over $K$, subject to: $\kappa_0 \cdot \mathrm{ofJ}(t)_M$ equals $W_A$ pushed forward along $A \hookrightarrow M$; $\Delta(W_A)$ is a unit in $A$; $e$ inverts the structure map $K \to A/\mathfrak{m}_A$ on every $c \in K$; $\gamma_0 \cdot (\widetilde{W_A}$ transported along $e)$ equals $E_0$; $\theta$ computes reduction, in the sense that whenever a point $P_1$ of $W_A$ over $M$ agrees (heterogeneously) with $\mathrm{vcInvFun}\,\kappa_0$ applied to $P$, then $\mathrm{reduceHom}\,h_\Delta\,P_1 = 0$ forces $\theta P = 0$, while $\mathrm{reduceHom}\,h_\Delta\,P_1 = (x,y)$ forces $\theta P$ to be the affine point with coordinates $\mathrm{vcXInv}\,\gamma_0\,(e\,x)$ and $\mathrm{vcYInv}\,\gamma_0\,(e\,x)\,(e\,y)$; $\theta$ is injective on $n$-torsion for every $n$ not divisible by $p$ (if $n \cdot P = 0$ and $\theta P = 0$ then $P = 0$); for every $\sigma \in \mathrm{Gal}(M/K(t))$ whose associated semilinear automorphism $(\sigma, \mathrm{id}_K)$ fixes $W_0$, $\rho\sigma$ stabilises $E_0$, $\rho$ is multiplicative on such $\sigma$, and $\mathrm{vcInvFun}\,(\rho\sigma)\,E_0 \circ \theta$ agrees (heterogeneously) with $\theta \circ \sigma$ on all points; conversely every variable change $\gamma$ with $\gamma \cdot E_0 = E_0$ is realised by some such $\sigma$, up to a global sign in the comparison of $\mathrm{vcInvFun}\,\gamma\,E_0 \circ \theta$ with $\theta \circ \sigma$; and $\rho\sigma = 1$ implies $\sigma = 1$ for such $\sigma$.
--
--   This is the Deuring–Serre–Tate statement that the generic elliptic curve of $j$-invariant $t$ acquires good reduction at every place of a suitable finite Galois extension $M/K(t)$ lying over a finite value $j_0$ of $j$, together with a Galois-equivariant identification of its prime-to-$p$ torsion with that of a curve $E_0/K$ of that $j$-invariant, realising every automorphism of $E_0$ up to sign by an element of the decomposition group; the level-$N$ points are simultaneously rational over $M$, and the place is arbitrary over an arbitrary $j_0$. It feeds the construction of moduli places and test data over the $j$-line, in particular the statements on integrality of $j$ at moduli places and on the order of vanishing of $j - j_0$ weighted by the size of the decomposition group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_equivariant_torsion_reduction_ofJ_forall_place_reduceHom.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_WeierstrassCurve_ReduceHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open scoped IntermediateField

universe u in

theorem ModularCurve.exists_equivariant_torsion_reduction_ofJ_forall_place_reduceHom
    (K : Type u) [Field K] [IsAlgClosed K] [DecidableEq K] (p : ℕ) [CharP K p]
    (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) :
    ∃ (M : Type u) (_ : Field M) (_ : DecidableEq M) (_ : Algebra K M) (t : M)
      (_ : Transcendental K t) (_ : FiniteDimensional K⟮t⟯ M) (_ : IsGalois K⟮t⟯ M),
      Nat.card {P : ((WeierstrassCurve.ofJ
        (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point //
          N • P = 0} = N ^ 2 ∧
      ∀ (j₀ : K) (E₀ : WeierstrassCurve K) [E₀.IsElliptic], E₀.j = j₀ →
      ∀ (W₀ : Place K M) [DecidableEq (ResidueField W₀.toValuationSubring)],
        0 < W₀.ord (t - algebraMap K M j₀) →
      ∃ (WA : WeierstrassCurve W₀.toValuationSubring) (κ₀ : VariableChange M)
        (e : ResidueField W₀.toValuationSubring ≃+* K) (γ₀ : VariableChange K)
        (hΔ : (WA.map (residue W₀.toValuationSubring)).Δ ≠ 0)
        (θ : ((WeierstrassCurve.ofJ
            (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point
          →+ E₀.toAffine.Point)
        (ρ : (M ≃ₐ[K⟮t⟯] M) → VariableChange K),
      κ₀ • (WeierstrassCurve.ofJ
          (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M =
        WA.map W₀.toValuationSubring.subtype ∧
      IsUnit WA.Δ ∧
      (∀ c : K, e (algebraMap K (ResidueField W₀.toValuationSubring) c) = c) ∧
      γ₀ • (WA.map (residue W₀.toValuationSubring)).map e.toRingHom = E₀ ∧
      (∀ (P : ((WeierstrassCurve.ofJ
            (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point)
          (P₁ : (WA.map W₀.toValuationSubring.subtype).toAffine.Point),
          HEq (Point.vcInvFun κ₀ ((WeierstrassCurve.ofJ
            (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine P) P₁ →
          reduceHom hΔ P₁ = 0 → θ P = 0) ∧
      (∀ (P : ((WeierstrassCurve.ofJ
            (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point)
          (P₁ : (WA.map W₀.toValuationSubring.subtype).toAffine.Point)
          (x y : ResidueField W₀.toValuationSubring)
          (h : (WA.map (residue W₀.toValuationSubring)).toAffine.Nonsingular x y),
          HEq (Point.vcInvFun κ₀ ((WeierstrassCurve.ofJ
            (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine P) P₁ →
          reduceHom hΔ P₁ = Point.some x y h →
          ∃ h' : E₀.toAffine.Nonsingular (vcXInv γ₀ (e x)) (vcYInv γ₀ (e x) (e y)),
            θ P = Point.some _ _ h') ∧
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
