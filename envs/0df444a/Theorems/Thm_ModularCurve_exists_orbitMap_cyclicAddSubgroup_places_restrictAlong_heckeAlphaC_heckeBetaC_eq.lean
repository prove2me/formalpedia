-- Prove2me | Theorems.Thm_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_restrictAlong_heckeAlphaC_heckeBetaC_eq
-- name    : ModularCurve.exists_orbitMap_cyclicAddSubgroup_places_restrictAlong_heckeAlphaC_heckeBetaC_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/969b7c8c-c2fd-5eee-aab6-2d06a4fe2397
-- title:
--   Places of X₀(M), X₀(Ms) and the two degeneracy laws
-- statement:
--   Let $K$ be an algebraically closed field, let $M\ge 1$ and let $s$ be a prime with $(Ms)\cdot 1\ne 0$ in $K$; assume the two $K$-algebra maps from $F_M=$ `modularFunctionFieldC K M` $=K(j(q),j(q^M))\subseteq K((q))$ into $R=$ `charLDegeneracyRoof K M s` $=K(j(q),j(q^M),j(q^s),j(q^{Ms}))$ — namely `heckeAlphaC`, the inclusion, and `heckeBetaC`, induced by the substitution $q\mapsto q^{s}$ — are integral, so that places may be restricted along them. Let $j_0\in K$ and let $E_0$ be an elliptic Weierstrass curve over $K$ with $j(E_0)=j_0$. The assertion is that there exist a map $g$ sending each Weierstrass curve $E$ over $K$ together with a cyclic subgroup $C$ of the affine points of $E$ with $|C|=M$ to a place of $F_M$ (a valuation subring containing $K$, proper, with principal ideals), and a map $f$ sending each cyclic subgroup $C$ of $E_0$ with $|C|=Ms$ to a place of $R$, such that: for elliptic $E$, $g(E,C)$ has positive order at $\mathrm{jGeomGen}-j(E)$, where $\mathrm{jGeomGen}$ is the $q$-expansion of $j$ viewed in $F_M$; every place of $F_M$ of positive order at $\mathrm{jGeomGen}-j(E)$ is of the form $g(E,C)$; $g(E,C)=g(E',C')$ precisely when some Weierstrass variable change $\gamma$ carries $E$ to $E'$ and sends every point of $C$ into $C'$; and the order of $\mathrm{jGeomGen}-j(E)$ at $g(E,C)$ equals the number of $C'$ with $g(E,C')=g(E,C)$. The same four statements hold for $f$ with respect to `heckeAlphaC`$(\mathrm{jGeomGen})-j_0$ in $R$, the identification condition now reading: some variable change fixes $E_0$ and maps $C$ into $C'$. Finally the two degeneracy laws: if every $T\in C$ satisfies $sT\in C'$ with $|C|=Ms$, $|C'|=M$, then the restriction of $f(C)$ along `heckeAlphaC` is $g(E_0,C')$; and, for $Q\in C$ of additive order $s$, the restriction of $f(C)$ along `heckeBetaC` is $g$ of the quotient curve at the image level structure, in two models — for odd $s=2n+1$ with the Vélu curve `E₀.veluQuotient (E₀.oddOrderSummingSet Q n)` of nonzero discriminant, for any homomorphism $\varphi$ on points with kernel $\mathbb Z Q$ given on points outside $\mathbb Z Q$ by Vélu's coordinate formulae `veluX`, `veluY`, and any cyclic $C''$ of order $M$ there containing $\varphi(C)$; and for arbitrary prime $s$ with the curve `E₀.fullKernelQuotient Q s` of nonzero discriminant, for any homomorphism $\varphi$ with kernel $\mathbb Z Q$ whose coordinates off $\mathbb Z Q$ are given by the translation sums $\sum_{k=1}^{s-1}\big((P+kQ)-(kQ)\big)$ added to those of $P$, and any cyclic $C''$ of order $M$ containing $\varphi(C)$.
--
--   This is the moduli dictionary for the function fields of $X_0(M)$ and $X_0(Ms)$ over an algebraically closed field in which $Ms$ is invertible: places above a given $j$-invariant correspond to isomorphism classes of pairs (elliptic curve, cyclic subgroup), with ramification measured by the size of the automorphism orbit, and the two degeneracy maps $\alpha,\beta\colon X_0(Ms)\to X_0(M)$ act on such pairs by $(E_0,C)\mapsto(E_0,sC)$ and $(E_0,C)\mapsto(E_0/C[s],\varphi(C))$ respectively. It is used in the analysis of widths of places in characteristic $\ell$ and in the computation of the Hecke operator $T_1$ on subgroup dual pairs, through [`ModularCurve.placeWidthChar_eq_one_of_restrictAlong_ne`](thm.html#ModularCurve.placeWidthChar_eq_one_of_restrictAlong_ne) and [`ModularCurve.ssHeckeMatrixC_one_apply_eq_natCard_subgroup_dualPair`](thm.html#ModularCurve.ssHeckeMatrixC_one_apply_eq_natCard_subgroup_dualPair).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_restrictAlong_heckeAlphaC_heckeBetaC_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_VeluPointMap
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Definitions.Def_WeierstrassCurve_FullKernelQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve WeierstrassCurve.Affine
open WeierstrassCurve

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_orbitMap_cyclicAddSubgroup_places_restrictAlong_heckeAlphaC_heckeBetaC_eq
    (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq K] (M s : ℕ) [NeZero M] [NeZero s]
    (hs : s.Prime) (hMs : ((M * s : ℕ) : K) ≠ 0)
    (hα : HeckeAlphaCIntegral K M s) (hβ : HeckeBetaCIntegral K M s)
    (j₀ : K) (E₀ : WeierstrassCurve K) [E₀.IsElliptic] (hE₀ : E₀.j = j₀) :
    ∃ (g : ∀ E : WeierstrassCurve K,
          {C : AddSubgroup E.toAffine.Point // IsAddCyclic C ∧ Nat.card C = M} →
            Place K (modularFunctionFieldC K M))
      (f : {C : AddSubgroup E₀.toAffine.Point // IsAddCyclic C ∧ Nat.card C = M * s} →
          Place K (charLDegeneracyRoof K M s)),

      (∀ (E : WeierstrassCurve K) [E.IsElliptic]
          (C : {C : AddSubgroup E.toAffine.Point // IsAddCyclic C ∧ Nat.card C = M}),
          0 < (g E C).ord (jGeomGen K M - algebraMap K (modularFunctionFieldC K M) E.j)) ∧

      (∀ (E : WeierstrassCurve K) [E.IsElliptic] (P : Place K (modularFunctionFieldC K M)),
          0 < P.ord (jGeomGen K M - algebraMap K (modularFunctionFieldC K M) E.j) →
            ∃ C : {C : AddSubgroup E.toAffine.Point // IsAddCyclic C ∧ Nat.card C = M}, g E C = P) ∧

      (∀ (E E' : WeierstrassCurve K) [E.IsElliptic] [E'.IsElliptic]
          (C : {C : AddSubgroup E.toAffine.Point // IsAddCyclic C ∧ Nat.card C = M})
          (C' : {C : AddSubgroup E'.toAffine.Point // IsAddCyclic C ∧ Nat.card C = M}),
          g E C = g E' C' ↔ ∃ γ : VariableChange K, γ • E = E' ∧
            ∀ T ∈ C.1, ∃ T' ∈ C'.1, HEq (Point.vcInvFun γ E.toAffine T) T') ∧

      (∀ (E : WeierstrassCurve K) [E.IsElliptic]
          (C : {C : AddSubgroup E.toAffine.Point // IsAddCyclic C ∧ Nat.card C = M}),
          (g E C).ord (jGeomGen K M - algebraMap K (modularFunctionFieldC K M) E.j) =
            (Nat.card {C' : {C : AddSubgroup E.toAffine.Point // IsAddCyclic C ∧ Nat.card C = M} //
              g E C' = g E C} : ℤ)) ∧

      (∀ C, 0 < (f C).ord (heckeAlphaC K M s (jGeomGen K M) -
          algebraMap K (charLDegeneracyRoof K M s) j₀)) ∧

      (∀ P : Place K (charLDegeneracyRoof K M s),
          0 < P.ord (heckeAlphaC K M s (jGeomGen K M) - algebraMap K (charLDegeneracyRoof K M s) j₀) →
            ∃ C, f C = P) ∧

      (∀ C C', f C = f C' ↔ ∃ γ : VariableChange K, γ • E₀ = E₀ ∧
          ∀ T ∈ C.1, ∃ T' ∈ C'.1, HEq (Point.vcInvFun γ E₀.toAffine T) T') ∧

      (∀ C, (f C).ord (heckeAlphaC K M s (jGeomGen K M) - algebraMap K (charLDegeneracyRoof K M s) j₀) =
          (Nat.card {C' : {C : AddSubgroup E₀.toAffine.Point // IsAddCyclic C ∧ Nat.card C = M * s} //
            f C' = f C} : ℤ)) ∧

      (∀ (C : {C : AddSubgroup E₀.toAffine.Point // IsAddCyclic C ∧ Nat.card C = M * s})
          (C' : {C : AddSubgroup E₀.toAffine.Point // IsAddCyclic C ∧ Nat.card C = M}),
          (∀ T ∈ C.1, s • T ∈ C'.1) →
            (f C).restrictAlong (heckeAlphaC K M s) hα = g E₀ C') ∧

      (∀ (C : {C : AddSubgroup E₀.toAffine.Point // IsAddCyclic C ∧ Nat.card C = M * s})
          (n : ℕ) (Q : E₀.toAffine.Point), s = 2 * n + 1 → Q ∈ C.1 → addOrderOf Q = 2 * n + 1 →
        (E₀.veluQuotient (E₀.oddOrderSummingSet Q n)).Δ ≠ 0 →
        ∀ φ : E₀.toAffine.Point →+ (E₀.veluQuotient (E₀.oddOrderSummingSet Q n)).toAffine.Point,
          φ.ker = AddSubgroup.zmultiples Q →
          (∀ (x y : K) (h : E₀.toAffine.Nonsingular x y),
            (.some x y h : E₀.toAffine.Point) ∉ AddSubgroup.zmultiples Q →
              ∃ h', φ (.some x y h) = .some (E₀.veluX (E₀.oddOrderSummingSet Q n) x)
                (E₀.veluY (E₀.oddOrderSummingSet Q n) x y) h') →
          ∀ C'' : {C : AddSubgroup (E₀.veluQuotient (E₀.oddOrderSummingSet Q n)).toAffine.Point //
              IsAddCyclic C ∧ Nat.card C = M},
            (∀ T ∈ C.1, φ T ∈ C''.1) →
              (f C).restrictAlong (heckeBetaC K M s) hβ =
                g (E₀.veluQuotient (E₀.oddOrderSummingSet Q n)) C'') ∧

      (∀ (C : {C : AddSubgroup E₀.toAffine.Point // IsAddCyclic C ∧ Nat.card C = M * s})
          (Q : E₀.toAffine.Point), Q ∈ C.1 → addOrderOf Q = s →
        (E₀.fullKernelQuotient Q s).Δ ≠ 0 →
        ∀ φ : E₀.toAffine.Point →+ (E₀.fullKernelQuotient Q s).toAffine.Point,
          φ.ker = AddSubgroup.zmultiples Q →
          (∀ P : E₀.toAffine.Point, P ∉ AddSubgroup.zmultiples Q →
            (φ P).coordsOrZero =
              (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (s - 1),
                  ((P + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1),
               P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (s - 1),
                  ((P + k • Q).coordsOrZero.2 - (k • Q).coordsOrZero.2))) →
          ∀ C'' : {C : AddSubgroup (E₀.fullKernelQuotient Q s).toAffine.Point //
              IsAddCyclic C ∧ Nat.card C = M},
            (∀ T ∈ C.1, φ T ∈ C''.1) →
              (f C).restrictAlong (heckeBetaC K M s) hβ = g (E₀.fullKernelQuotient Q s) C'') := by sorry
