-- Prove2me | Theorems.Thm_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ
-- name    : ModularCurve.exists_frobeniusSemilinear_torsionModel_ofJ_univ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/4800b1f9-0434-591a-82bb-43f3d9755fe2
-- title:
--   Frobenius-semilinear level-N model of the generic elliptic curve
-- statement:
--   Let $K$ be an algebraically closed field of characteristic a prime $q$, let $N$ be a natural number with $N \neq 0$ in $K$, and let $E_0$ be an elliptic Weierstrass curve over $K$ whose coefficients are fixed by the $q$-th power map, i.e. $E_0$ mapped along `frobenius K q` equals $E_0$. Then there are: a field $M$ (in the same universe) that is a $K$-algebra, an element $t \in M$ transcendental over $K$ with $M$ finite-dimensional and Galois over $K\langle t\rangle$; a place $W_0$ of $M$ over $K$ (a proper valuation subring of $M$ containing the image of $K$ and a principal ideal ring) with $\mathrm{ord}_{W_0}(t - j(E_0)) > 0$; writing $E_t$ for `WeierstrassCurve.ofJ t` over $K\langle t\rangle$ base-changed to $M$, an additive map $\theta$ from the affine points of $E_t$ to those of $E_0$; a map $\rho$ from $\mathrm{Gal}(M/K\langle t\rangle)$ to variable changes over $K$; a bijection $\Phi$ between the cyclic subgroups of $E_t(M)$ of cardinality $N$ and the $K$-algebra homomorphisms $\psi$ from `modularFunctionFieldFullC K N` (the subfield of `LaurentSeries K` generated over $K$ by the series `qExpand K d (jqModC K)` for the nonzero divisors $d$ of $N$) to $M$ with $\psi(\mathrm{jqModC}) = t$; a semilinear automorphism $\mathrm{fr}_M$ of $M$ over $K$ (a pair of ring automorphisms of $M$ and of $K$ compatible with the structure map); additive endomorphisms $\mathrm{fr}_E$ of $E_t(M)$ and $\mathrm{fr}_0$ of $E_0(K)$; and an integer $\varepsilon$, subject to the following. The set of $P$ with $N \cdot P = 0$ in $E_t(M)$ has cardinality $N^2$; if $q \nmid n$, $n \cdot P = 0$ and $\theta P = 0$ then $P = 0$; for every $\sigma \in \mathrm{Gal}(M/K\langle t\rangle)$ whose associated semilinear automorphism fixes $W_0$, the variable change $\rho\sigma$ stabilises $E_0$ and $\theta$ intertwines $\sigma$ on $E_t(M)$ with the point map `Point.vcInvFun (ρ σ)` on $E_0$ (an equality of terms asserted as a heterogeneous equality); conversely every variable change $\gamma$ with $\gamma \cdot E_0 = E_0$ is realised, up to a global sign, by some such $\sigma$; $\Phi$ is equivariant, in that $H' = \sigma(H)$ implies $\Phi H' = \Phi H$ followed by $\sigma$ viewed as a $K$-algebra map; $\mathrm{fr}_M$ acts on scalars by $a \mapsto a^q$ and fixes both $t$ and $W_0$; $\mathrm{fr}_E$ sends an affine point $(x,y)$ to $(\mathrm{fr}_M x, \mathrm{fr}_M y)$ and $\mathrm{fr}_0$ sends $(x,y)$ to $(x^q, y^q)$; $\varepsilon = \pm 1$ and $\theta(\mathrm{fr}_E P) = \varepsilon \cdot \mathrm{fr}_0(\theta P)$ for all $N$-torsion $P$; and finally, if $H' = \mathrm{fr}_E(H)$ then for every nonzero divisor $d$ of $N$ the value of $\Phi H'$ at `qExpand K d (jqModC K)` is $\mathrm{fr}_M$ applied to the value of $\Phi H$ there.
--
--   This is the reduction-theoretic input in the style of Deuring: the generic elliptic curve with $j$-invariant a transcendental $t$ is given a model over a finite Galois extension of $K(t)$ together with a place specialising $t$ to $j(E_0)$, a specialisation map on points compatible with automorphisms of $E_0$, and a dictionary between cyclic subgroups of order $N$ and embeddings of the full level-$N$ modular function field, all compatible with a $q$-power Frobenius up to a sign. It is used to compare places of the modular function field with the arithmetic Frobenius on moduli points, in [`ModularCurve.exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ`](thm.html#ModularCurve.exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ.lean

import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve WeierstrassCurve WeierstrassCurve.Affine
open scoped IntermediateField
universe u in

theorem ModularCurve.exists_frobeniusSemilinear_torsionModel_ofJ_univ
    (K : Type u) [Field K] [IsAlgClosed K] [DecidableEq K] (q : ℕ) [Fact q.Prime] [CharP K q]
    (N : ℕ) (hN : (N : K) ≠ 0)
    (E₀ : WeierstrassCurve K) [E₀.IsElliptic] (hfr : E₀.map (frobenius K q) = E₀) :
    ∃ (M : Type u) (_ : Field M) (_ : DecidableEq M) (_ : Algebra K M) (t : M)
      (_ : Transcendental K t) (_ : FiniteDimensional K⟮t⟯ M) (_ : IsGalois K⟮t⟯ M)
      (W₀ : Place K M) (_ : 0 < W₀.ord (t - algebraMap K M E₀.j))
      (θ : ((WeierstrassCurve.ofJ
            (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point
          →+ E₀.toAffine.Point)
      (ρ : (M ≃ₐ[K⟮t⟯] M) → VariableChange K)
      (Φ : {H : AddSubgroup ((WeierstrassCurve.ofJ
              (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point //
              IsAddCyclic H ∧ Nat.card H = N} ≃
            {ψ : modularFunctionFieldFullC K N →ₐ[K] M // ψ ⟨jqModC K, jqModC_mem_full K N⟩ = t})
      (frM : SemilinearAut K M)
      (frE : ((WeierstrassCurve.ofJ
            (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point
          →+ ((WeierstrassCurve.ofJ
            (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point)
      (fr₀ : E₀.toAffine.Point →+ E₀.toAffine.Point) (ε : ℤ),
      Nat.card {P : ((WeierstrassCurve.ofJ
        (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point //
          N • P = 0} = N ^ 2 ∧
      (∀ (n : ℕ) (P : ((WeierstrassCurve.ofJ
          (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point),
          ¬ q ∣ n → n • P = 0 → θ P = 0 → P = 0) ∧
      (∀ σ : M ≃ₐ[K⟮t⟯] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ →
          ρ σ • E₀ = E₀) ∧
      (∀ σ : M ≃ₐ[K⟮t⟯] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ →
          ∀ P, HEq (Point.vcInvFun (ρ σ) E₀.toAffine (θ P))
            (θ (WeierstrassCurve.Affine.Point.map (σ : M →ₐ[K⟮t⟯] M) P))) ∧
      (∀ γ : VariableChange K, γ • E₀ = E₀ →
          ∃ σ : M ≃ₐ[K⟮t⟯] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ ∧
            ((∀ P, HEq (Point.vcInvFun γ E₀.toAffine (θ P))
                (θ (WeierstrassCurve.Affine.Point.map (σ : M →ₐ[K⟮t⟯] M) P))) ∨
             (∀ P, HEq (Point.vcInvFun γ E₀.toAffine (θ P))
                (-θ (WeierstrassCurve.Affine.Point.map (σ : M →ₐ[K⟮t⟯] M) P))))) ∧
      (∀ (σ : M ≃ₐ[K⟮t⟯] M) (H H' : {H : AddSubgroup ((WeierstrassCurve.ofJ
          (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point //
          IsAddCyclic H ∧ Nat.card H = N}),
        H'.1 = H.1.map (WeierstrassCurve.Affine.Point.map (σ : M →ₐ[K⟮t⟯] M)) →
          ((Φ H').1 : modularFunctionFieldFullC K N →ₐ[K] M) =
            ((σ : M →ₐ[K⟮t⟯] M).restrictScalars K).comp (Φ H).1) ∧
      (∀ a : K, frM • (algebraMap K M a) = algebraMap K M (a ^ q)) ∧
      frM • t = t ∧
      frM • W₀ = W₀ ∧
      (∀ (x y : M) (h : ((WeierstrassCurve.ofJ
          (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Nonsingular x y),
        ∃ h', frE (.some x y h) = .some (frM • x) (frM • y) h') ∧
      (∀ (x y : K) (h : E₀.toAffine.Nonsingular x y), ∃ h', fr₀ (.some x y h) = .some (x ^ q) (y ^ q) h') ∧
      (ε = 1 ∨ ε = -1) ∧
      (∀ P : ((WeierstrassCurve.ofJ
          (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point,
        N • P = 0 → θ (frE P) = ε • fr₀ (θ P)) ∧
      (∀ (H H' : {H : AddSubgroup ((WeierstrassCurve.ofJ
          (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point //
          IsAddCyclic H ∧ Nat.card H = N}),
        H'.1 = H.1.map frE →
          ∀ (d : ℕ) [NeZero d] (hd : d ∣ N),
            (Φ H').1 ⟨qExpand K d (jqModC K), jqModCd_mem_full K N hd⟩ =
              frM • ((Φ H).1 ⟨qExpand K d (jqModC K), jqModCd_mem_full K N hd⟩)) := by sorry
