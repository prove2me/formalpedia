-- Prove2me | Theorems.Thm_ModularCurve_moduliPlace_restrictAlong_qExpand_veluQuotient
-- name    : ModularCurve.moduliPlace_restrictAlong_qExpand_veluQuotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/08fc645b-4abf-5ec4-94ca-d8a22de4d1a0
-- title:
--   Second degeneracy map on moduli places via Vélu's odd-order model
-- statement:
--   Let $K$ be an algebraically closed field and $M,s$ nonzero natural numbers with $Ms \neq 0$ in $K$. For a level $N$, `modularFunctionFieldFullC K N` is the subfield of $K((q))$ generated over $K$ by the expansions `divisorExpansionsC K N`, and a place of it is a valuation subring containing $K$, distinct from the whole field and a principal ideal ring. Assume: places satisfying `IsModuliPlaceOf` at level $M$ (those whose valuation subring is the pull-back along the embedding of a `ModuliTestDatum` of the valuation subring of a place of the ambient field) are unique for each point of `ModuliPoint M K`, and at level $Ms$ such a place exists for every point; $\beta$ is a $K$-algebra map from level $M$ to level $Ms$ acting on $q$-expansions by `qExpand K s`, i.e. $q \mapsto q^{s}$ (multiplication of exponents by $s$), and is integral. Let $E_0/K$ be an elliptic Weierstrass curve, $C \leq E_0(K)$ cyclic with $\#C = Ms$, let $s = 2n+1$, and let $Q \in C$ have additive order $2n+1$. Write $E_1 =$ `E₀.veluQuotient (E₀.oddOrderSummingSet Q n)`, Vélu's Weierstrass curve whose $a_1,a_2,a_3$ agree with those of $E_0$ and whose $a_4, a_6$ are corrected by the Vélu sums over the coordinates of $Q,2Q,\dots,nQ$; assume its discriminant is nonzero. Let $\varphi : E_0(K) \to E_1(K)$ be an additive map with kernel the multiples of $Q$ which on every affine point outside $\langle Q\rangle$ is given by the Vélu formulae `veluX`, `veluY`. Let $C'' \leq E_1(K)$ be cyclic of order $M$ with $\varphi(C) \subseteq C''$. Then the pull-back along $\beta$ of the valuation subring of `moduliPlace K (M * s) E₀ C` is `moduliPlace K M E₁ C''`.
--
--   This is the moduli interpretation of the second degeneracy map $X_0(Ms) \to X_0(M)$, $(E,C) \mapsto (E/C[s], C/C[s])$, stated for places of the $q$-expansion function fields with the quotient realised by Vélu's equations for a cyclic subgroup of odd order $s$. It is used in the computation of the Hecke correspondence on moduli places, in particular in the determination of ramification indices along the degeneracy maps and in the identification of the images of cyclic subgroups under them.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_moduliPlace_restrictAlong_qExpand_veluQuotient.lean

import Mathlib
import Definitions.Def_ModularCurve_ModuliPlace
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_VeluQuotientMap
import Definitions.Def_WeierstrassCurve_VeluPointMap
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve WeierstrassCurve WeierstrassCurve.Affine

universe u in

theorem ModularCurve.moduliPlace_restrictAlong_qExpand_veluQuotient
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
    (E₀ : WeierstrassCurve K) [E₀.IsElliptic]
    (C : AddSubgroup E₀.toAffine.Point) (hC : IsAddCyclic C ∧ Nat.card C = M * s)
    (n : ℕ) (hs : s = 2 * n + 1) (Q : E₀.toAffine.Point) (hQC : Q ∈ C)
    (hQ : addOrderOf Q = 2 * n + 1)
    (hΔ : (E₀.veluQuotient (E₀.oddOrderSummingSet Q n)).Δ ≠ 0)
    (φ : E₀.toAffine.Point →+ (E₀.veluQuotient (E₀.oddOrderSummingSet Q n)).toAffine.Point)
    (hφker : φ.ker = AddSubgroup.zmultiples Q)
    (hφ : ∀ (x y : K) (h : E₀.toAffine.Nonsingular x y),
      (.some x y h : E₀.toAffine.Point) ∉ AddSubgroup.zmultiples Q →
        ∃ h', φ (.some x y h) = .some (E₀.veluX (E₀.oddOrderSummingSet Q n) x)
          (E₀.veluY (E₀.oddOrderSummingSet Q n) x y) h')
    (C'' : AddSubgroup (E₀.veluQuotient (E₀.oddOrderSummingSet Q n)).toAffine.Point)
    (hC'' : IsAddCyclic C'' ∧ Nat.card C'' = M) (hCC'' : ∀ T ∈ C, φ T ∈ C'') :
    (moduliPlace K (M * s) E₀ C).restrictAlong β hb =
      moduliPlace K M (E₀.veluQuotient (E₀.oddOrderSummingSet Q n)) C'' := by sorry
