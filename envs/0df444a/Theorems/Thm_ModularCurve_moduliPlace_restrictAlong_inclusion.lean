-- Prove2me | Theorems.Thm_ModularCurve_moduliPlace_restrictAlong_inclusion
-- name    : ModularCurve.moduliPlace_restrictAlong_inclusion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/a6eb02cc-3c2a-583a-b7c7-b0fae1eefed3
-- title:
--   Degeneracy law for moduli places: level N down to M
-- statement:
--   Let $K$ be a field and let $M$ and $N$ be positive integers with $M \mid N$. For a positive integer $n$ write $F_n =$ `modularFunctionFieldFullC K n` for the intermediate field of $K((q))$ obtained by adjoining to $K$ all elements `qExpand K d (jqModC K)` with $d$ a positive divisor of $n$; the hypothesis $M \mid N$ gives, through `full_degeneracyC_le`, an inclusion $F_M \subseteq F_N$, and `IntermediateField.inclusion` the corresponding $K$-algebra map. Three hypotheses are assumed: (i) every $x$ in `ModuliPoint N K` — the quotient of the pairs $(E,g)$ consisting of an elliptic Weierstrass curve $E$ over $K$ and a point $g \in E(K)$ of exact additive order $N$, modulo variable changes of the Weierstrass model combined with replacing $g$ by $kg$ for $k$ coprime to $N$ — admits some place $v$ of $F_N$ over $K$ (a valuation subring containing the image of $K$, distinct from $F_N$ and a principal ideal ring) with `IsModuliPlaceOf K N x v`, i.e. whose valuation subring is the preimage, along the embedding `emb` of some moduli test datum $D$ for $x$ into some $K$-algebra field $\Omega$, of the valuation subring of $D$'s place of $\Omega$; (ii) at level $M$ such a place is unique: any two places of $F_M$ satisfying `IsModuliPlaceOf K M x` for the same $x$ coincide; (iii) the inclusion $F_M \hookrightarrow F_N$ is an integral ring homomorphism, so that places of $F_N$ may be restricted along it, the restriction being the preimage of the valuation subring. Let finally $E$ be a Weierstrass curve over $K$, let $C \subseteq E(K)$ be an additively cyclic subgroup with $\#C = N$, let $C' \subseteq E(K)$ be an additively cyclic subgroup with $\#C' = M$, and assume $(N/M)\cdot T \in C'$ for every $T \in C$. Then the restriction along $F_M \hookrightarrow F_N$ of `moduliPlace K N E C` equals `moduliPlace K M E C'`, where `moduliPlace K n E D` denotes the place of $F_n$ attached to the moduli point of $(E,g)$ for a chosen generator $g$ of $D$ of order $n$ when $E$ is elliptic and such a generator exists, and the $q$-adic place at infinity otherwise.
--
--   This is the moduli-theoretic description, transported to places of the modular function fields, of the first (level-forgetting) degeneracy map $\pi_1 : X_0(N) \to X_0(M)$: pulling a function of level $M$ back to level $N$ and evaluating at $(E,C)$ agrees with evaluating at $(E,(N/M)C)$. Together with the companion statement for the second degeneracy map it underlies the treatment of Hecke correspondences on modular curves, and it is used in the analysis of Hecke and level-structure correspondences and in the Čerednik–Drinfeld part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_moduliPlace_restrictAlong_inclusion.lean

import Mathlib
import Definitions.Def_ModularCurve_ModuliPlace
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve WeierstrassCurve WeierstrassCurve.Affine

universe u in

theorem ModularCurve.moduliPlace_restrictAlong_inclusion
    (K : Type u) [Field K] [DecidableEq K] (N M : ℕ) [NeZero N] [NeZero M] (hMN : M ∣ N)
    (hex : ∀ x : ModuliPoint N K, ∃ v, IsModuliPlaceOf K N x v)
    (huniq : ∀ (x : ModuliPoint M K) (v v' : Place K ↥(modularFunctionFieldFullC K M)),
      IsModuliPlaceOf K M x v → IsModuliPlaceOf K M x v' → v = v')
    (hι : (IntermediateField.inclusion (full_degeneracyC_le K hMN)).toRingHom.IsIntegral)
    (E : WeierstrassCurve K)
    (C : {C : AddSubgroup E.toAffine.Point // IsAddCyclic C ∧ Nat.card C = N})
    (C' : {C : AddSubgroup E.toAffine.Point // IsAddCyclic C ∧ Nat.card C = M})
    (hCC' : ∀ T ∈ C.1, (N / M) • T ∈ C'.1) :
    (moduliPlace K N E C.1).restrictAlong
        (IntermediateField.inclusion (full_degeneracyC_le K hMN)) hι =
      moduliPlace K M E C'.1 := by sorry
