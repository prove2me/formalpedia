-- Prove2me | Theorems.Thm_ModularCurve_moduliPlace_restrictAlong_qExpand_fullKernelQuotient
-- name    : ModularCurve.moduliPlace_restrictAlong_qExpand_fullKernelQuotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/cc50fd3a-6d4f-5083-aa83-de57ed7d482a
-- title:
--   Second degeneracy map on moduli places: (E,C)↦(E/⟨ Q⟩,φ C)
-- statement:
--   Let $K$ be an algebraically closed field with decidable equality, and let $M,s\ge 1$ be natural numbers with $(Ms)\cdot 1_K\neq 0$. Write $F_N$ for `modularFunctionFieldFullC K N`, the subfield of $K((q))$ generated over $K$ by the divisor expansions at level $N$, and recall that a `Place K F` is a valuation subring of $F$ containing the image of $K$, distinct from $F$, and a principal ideal ring; `moduliPlace K N E C` is the chosen moduli place of the class of $(E,g)$ when $E$ is elliptic and $C=\langle g\rangle$ for some $g$ of additive order $N$ (a place $v$ of $F_N$ being a moduli place of a class $x$ when its valuation subring is the preimage, under the embedding supplied by a moduli test datum for $x$ over some $K$-field $\Omega$, of the valuation subring of that datum's place of $\Omega$), and is the $q$-adic place at infinity otherwise. Assume: any two moduli places of one and the same level-$M$ moduli point coincide; every level-$Ms$ moduli point over $K$ admits a moduli place; $\beta\colon F_M\to F_{Ms}$ is a $K$-algebra homomorphism which on underlying Laurent series is the substitution $q\mapsto q^{s}$, i.e. `qExpand K s` (re-indexing exponents by multiplication by $s$), and $\beta$ is integral as a ring map. Let $E$ be an elliptic Weierstrass curve over $K$, $C\le E(K)$ cyclic with $\#C=Ms$, and $Q\in C$ of exact additive order $s$; assume the Vélu quotient $E'=$ `E.fullKernelQuotient Q s` has $\Delta\neq 0$, and let $\varphi\colon E(K)\to E'(K)$ be an additive map with kernel $\langle Q\rangle$ whose coordinates, at points off $\langle Q\rangle$, are given by Vélu's sums $\sum_{k=1}^{s-1}$ of the coordinatewise differences of $P+kQ$ and $kQ$ added to those of $P$. Let $C''\le E'(K)$ be cyclic with $\#C''=M$ and $\varphi(C)\subseteq C''$. Then the place of $F_M$ obtained by restricting `moduliPlace K (M * s) E C` along $\beta$ (the preimage of its valuation subring under $\beta$) equals `moduliPlace K M E' C''`.
--
--   This is the modular interpretation of the second degeneracy map $\pi_2\colon X_0(Ms)\to X_0(M)$, $(E,C)\mapsto (E/C[s],C/C[s])$, expressed at the level of places of the function fields over an algebraically closed field of characteristic prime to $Ms$, with Vélu's explicit model and isogeny in place of the abstract quotient. It feeds the computations of ramification indices and of the Hecke correspondence on moduli places, such as [`ModularCurve.finsum_ramificationIndexAlong_heckeAlphaC_eq_natCard_overgroup_dualPair_of_moduliPlace`](thm.html#ModularCurve.finsum_ramificationIndexAlong_heckeAlphaC_eq_natCard_overgroup_dualPair_of_moduliPlace) and [`ModularCurve.exists_orbitMap_cyclicAddSubgroup_places_restrictAlong_heckeAlphaC_heckeBetaC_eq`](thm.html#ModularCurve.exists_orbitMap_cyclicAddSubgroup_places_restrictAlong_heckeAlphaC_heckeBetaC_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_moduliPlace_restrictAlong_qExpand_fullKernelQuotient.lean

import Mathlib
import Definitions.Def_ModularCurve_ModuliPlace
import Definitions.Def_WeierstrassCurve_FullKernelQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve WeierstrassCurve WeierstrassCurve.Affine

universe u in

theorem ModularCurve.moduliPlace_restrictAlong_qExpand_fullKernelQuotient
    (K : Type u) [Field K] [IsAlgClosed K] [DecidableEq K] (M s : ℕ) [NeZero M] [NeZero s]
    (hMs : ((M * s : ℕ) : K) ≠ 0)
    (huniq : ∀ (x : ModuliPoint M K) (v v' : Place K (modularFunctionFieldFullC K M)),
      IsModuliPlaceOf K M x v → IsModuliPlaceOf K M x v' → v = v')
    (hex : ∀ x : ModuliPoint (M * s) K, ∃ v, IsModuliPlaceOf K (M * s) x v)
    (β : modularFunctionFieldFullC K M →ₐ[K] modularFunctionFieldFullC K (M * s))
    (hβ : ∀ f : modularFunctionFieldFullC K M,
      ((β f : modularFunctionFieldFullC K (M * s)) : LaurentSeries K) =
        qExpand K s (f : LaurentSeries K))
    (hb : β.toRingHom.IsIntegral)
    (E : WeierstrassCurve K) [E.IsElliptic]
    (C : AddSubgroup E.toAffine.Point) (hC : IsAddCyclic C ∧ Nat.card C = M * s)
    (Q : E.toAffine.Point) (hQC : Q ∈ C) (hQ : addOrderOf Q = s)
    (hΔ : (E.fullKernelQuotient Q s).Δ ≠ 0)
    (φ : E.toAffine.Point →+ (E.fullKernelQuotient Q s).toAffine.Point)
    (hφker : φ.ker = AddSubgroup.zmultiples Q)
    (hφ : ∀ P : E.toAffine.Point, P ∉ AddSubgroup.zmultiples Q →
      (φ P).coordsOrZero =
        (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (s - 1),
            ((P + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1),
         P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (s - 1),
            ((P + k • Q).coordsOrZero.2 - (k • Q).coordsOrZero.2)))
    (C'' : AddSubgroup (E.fullKernelQuotient Q s).toAffine.Point)
    (hC'' : IsAddCyclic C'' ∧ Nat.card C'' = M) (hCC'' : ∀ T ∈ C, φ T ∈ C'') :
    (moduliPlace K (M * s) E C).restrictAlong β hb =
      moduliPlace K M (E.fullKernelQuotient Q s) C'' := by sorry
