-- Prove2me | Theorems.Thm_ModularCurve_exists_equiv_algHom_modularFunctionFieldFullC_apply_jqNModC_eq_fullKernelQuotient_j
-- name    : ModularCurve.exists_equiv_algHom_modularFunctionFieldFullC_apply_jqNModC_eq_fullKernelQuotient_j
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/33f3eb4c-78a9-5ae8-b8b1-5bafc61bb1c2
-- title:
--   Kronecker dictionary: Φ(H) carries j(q^N) to j(E/H)
-- statement:
--   Let $K$ be an algebraically closed field and $N$ a nonzero natural number with $(N:K)\neq 0$; let $k \subseteq \Omega$ be fields forming a scalar tower over $K$, and let $E$ be a Weierstrass curve over $k$ that is elliptic, whose $j$-invariant is transcendental over $K$, and such that the group of points $P$ of $E$ base-changed to $\Omega$ with $N \cdot P = 0$ has exactly $N^2$ elements. Write $F =$ `modularFunctionFieldFullC K N` for the intermediate field of the Laurent series field over $K$ generated over $K$ by the series $q \mapsto q^d$ substituted into `jqModC K` $= q^{-1}\cdot E_4^3\cdot(\text{inverse Dedekind eta unit})$, for all nonzero divisors $d \mid N$. The assertion is that there exists a bijection $\Phi$ from the set of subgroups $H$ of the point group of $E$ over $\Omega$ that are cyclic with $\#H = N$ onto the set of $K$-algebra homomorphisms $\psi : F \to \Omega$ with $\psi(\mathtt{jqModC } K) = j(E)$ (image under $k \to \Omega$), subject to two conditions: (i) for every $k$-algebra automorphism $\sigma$ of $\Omega$ and all such $H, H'$ with $H'$ the image of $H$ under the map on points induced by $\sigma$, one has $\Phi(H') = \Phi(H)$ followed by $\sigma$, as $K$-algebra homomorphisms; and (ii) for every such $H$ and every point $Q$ with $H$ the group of integer multiples of $Q$ and $Q$ of additive order $N$, provided the Weierstrass curve `(E.baseChange Ω).fullKernelQuotient Q N` — the curve with the same $a_1, a_2, a_3$ and with $a_4 - 5t$, $a_6 - b_2 t - 7w$, where $t$ and $w$ are the Vélu sums $\sum (3x^2 + 2a_2x + a_4 - a_1y)$ and $\sum (x(3x^2+2a_2x+a_4-a_1y) + y(2y+a_1x+a_3))$ over the coordinates of $k\cdot Q$ for $1 \le k \le N-1$ — has nonzero discriminant, $\Phi(H)$ sends the element `jqNModC K N` (the substitution $q \mapsto q^N$ in `jqModC K`) to the $j$-invariant of that quotient curve.
--
--   This is Igusa's form of Kronecker's theorem on the modular equation $\Phi_N$, in the shape of a single equivariant dictionary between cyclic subgroups of order $N$ of the $N$-torsion and embeddings of the full level-$N$ modular function field: the first coordinate $j(q)$ records $j(E)$ and the second coordinate $j(q^N)$ records the $j$-invariant of the Vélu quotient by the subgroup. It is used in the study of places of the modular function field and of ramification indices along them, and in the identification of torsion reduction data with evaluation of modular functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_equiv_algHom_modularFunctionFieldFullC_apply_jqNModC_eq_fullKernelQuotient_j.lean

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_WeierstrassCurve_FullKernelQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve WeierstrassCurve
universe u v in

theorem ModularCurve.exists_equiv_algHom_modularFunctionFieldFullC_apply_jqNModC_eq_fullKernelQuotient_j
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
      (∀ (H : {H : AddSubgroup (E.baseChange Ω).toAffine.Point // IsAddCyclic H ∧ Nat.card H = N})
          (Q : (E.baseChange Ω).toAffine.Point), H.1 = AddSubgroup.zmultiples Q → addOrderOf Q = N →
          ∀ hΔ : ((E.baseChange Ω).fullKernelQuotient Q N).Δ ≠ 0,
            (Φ H).1 ⟨jqNModC K N, jqModCd_mem_full K N (dvd_refl N)⟩ =
              @WeierstrassCurve.j Ω _ ((E.baseChange Ω).fullKernelQuotient Q N) ⟨isUnit_iff_ne_zero.mpr hΔ⟩) := by sorry
