-- Prove2me | Theorems.Thm_ModularCurve_exists_equiv_algHom_modularFunctionFieldFullC_apply_jqN_eq_cyclicQuotientJ
-- name    : ModularCurve.exists_equiv_algHom_modularFunctionFieldFullC_apply_jqN_eq_cyclicQuotientJ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/28417af0-d11e-57ad-8f8c-de537c8d8566
-- title:
--   Cyclic N-subgroups versus embeddings of the modular function field
-- statement:
--   Let $K$ be an algebraically closed field, $N$ a positive natural number with $N \neq 0$ in $K$, and let $k \subseteq \Omega$ be fields equipped with $K$-algebra structures forming a scalar tower over $K$. Let $E$ be a Weierstrass curve over $k$ which is elliptic, assume its invariant $E.j$ is transcendental over $K$, and assume the group of $\Omega$-points of the affine curve obtained from $E$ by base change to $\Omega$ has exactly $N^2$ elements killed by $N$. Write $\mathrm{jq} =$ `jqModC K` for the Laurent series $q^{-1}\cdot\sum$ (the image over $K$ of the power series $E_4^3\eta^{-24}$), `qExpand K d` for the ring endomorphism of $K$-Laurent series multiplying exponents by $d$ (substitution $q \mapsto q^d$), and `modularFunctionFieldFullC K N` for the intermediate field of $K((q))$ generated over $K$ by the series `qExpand K d (jqModC K)` for all positive divisors $d \mid N$. The assertion is that there is a bijection $\Phi$ from the set of additively cyclic subgroups $H$ of the $\Omega$-points of $E$ of cardinality $N$ onto the set of $K$-algebra homomorphisms $\psi :$ `modularFunctionFieldFullC K N` $\to \Omega$ with $\psi(\mathrm{jq}) =$ the image of $E.j$ in $\Omega$, such that: (i) for every $k$-algebra automorphism $\sigma$ of $\Omega$ and every such $H, H'$ with $H'$ the image of $H$ under the map on points induced by $\sigma$, one has $\Phi(H') = \Phi(H)$ followed by $\sigma$ (as $K$-algebra homomorphisms); and (ii) for every algebraically closed field $L$ which is an algebra over $k$ and over $\Omega$ compatibly, and every such $H$, the image in $L$ of $\Phi(H)\big(\mathrm{qExpand}\ K\ N\ (\mathrm{jq})\big)$ equals `cyclicQuotientJ` of the base change of $E$ to $L$ at the image of $H$ under the map on points induced by $\Omega \to L$ and at $N$, i.e. $c_4^3/\Delta$ of the Weierstrass curve `cyclicQuotientCurve` attached to that subgroup.
--
--   This is Igusa's form of Kronecker's theorem on the modular equation, enriched by the modular interpretation of the generator $j(q^N)$: the embeddings of the level-$N$ modular function field extending $j \mapsto j(E)$ correspond to the cyclic subgroups of order $N$ of $E$, equivariantly for $\mathrm{Aut}(\Omega/k)$, and the second coordinate $j(q^N)$ specialises to the invariant of the quotient curve $E/H$. It is used by [`ModularCurve.exists_equiv_algHom_modularFunctionFieldFullC_forall_dvd_apply_jqNModC_eq_cyclicQuotientJ`](thm.html#ModularCurve.exists_equiv_algHom_modularFunctionFieldFullC_forall_dvd_apply_jqNModC_eq_cyclicQuotientJ), which records the values of all the generators $j(q^d)$, $d \mid N$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_equiv_algHom_modularFunctionFieldFullC_apply_jqN_eq_cyclicQuotientJ.lean

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_WeierstrassCurve_CyclicQuotientJ

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve WeierstrassCurve WeierstrassCurve.Affine

universe u v w in

theorem ModularCurve.exists_equiv_algHom_modularFunctionFieldFullC_apply_jqN_eq_cyclicQuotientJ
    (K : Type u) [Field K] [IsAlgClosed K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)
    (k Ω : Type v) [Field k] [Field Ω] [DecidableEq Ω] [Algebra K k] [Algebra K Ω] [Algebra k Ω]
    [IsScalarTower K k Ω] (E : WeierstrassCurve k) [E.IsElliptic]
    (hE : Transcendental K E.j)
    (hfull : Nat.card {P : (E.baseChange Ω).toAffine.Point // N • P = 0} = N ^ 2) :
    ∃ Φ : {H : AddSubgroup (E.baseChange Ω).toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} ≃
        {ψ : modularFunctionFieldFullC K N →ₐ[K] Ω //
          ψ ⟨jqModC K, jqModC_mem_full K N⟩ = algebraMap k Ω E.j},
      (∀ (σ : Ω ≃ₐ[k] Ω) (H H' : {H : AddSubgroup (E.baseChange Ω).toAffine.Point //
          IsAddCyclic H ∧ Nat.card H = N}),
        H'.1 = H.1.map (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω)) →
          ((Φ H').1 : modularFunctionFieldFullC K N →ₐ[K] Ω) =
            ((σ : Ω →ₐ[k] Ω).restrictScalars K).comp (Φ H).1) ∧
      ∀ (L : Type w) [Field L] [DecidableEq L] [IsAlgClosed L] [Algebra k L] [Algebra Ω L]
        [IsScalarTower k Ω L]
        (H : {H : AddSubgroup (E.baseChange Ω).toAffine.Point // IsAddCyclic H ∧ Nat.card H = N}),
        algebraMap Ω L ((Φ H).1 ⟨qExpand K N (jqModC K), jqModCd_mem_full K N dvd_rfl⟩) =
          (E.baseChange L).cyclicQuotientJ
            (H.1.map (WeierstrassCurve.Affine.Point.map (IsScalarTower.toAlgHom k Ω L))) N := by sorry
