-- Prove2me | Theorems.Thm_M4aHerbrand_isZero_groupCohomology_unitIdelesTrivialOn_of_ramificationIdx_eq_one
-- name    : M4aHerbrand.isZero_groupCohomology_unitIdelesTrivialOn_of_ramificationIdx_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/447101e0-c1cd-516b-9870-bd54e0b3317b
-- title:
--   Vanishing of positive-degree cohomology of unit idèles outside T
-- statement:
--   Let $E \subseteq F$ be number fields (as `Field`s with `NumberField` structure and an $E$-algebra structure on $F$) with $F/E$ Galois, and write $G = F \simeq_{\mathrm{alg}[E]} F$ for its Galois group. Let $D$ be an `IdeleGaloisDescent` datum for $(\mathcal{O}_F, E, F)$, that is, a monoid homomorphism $D.\mathrm{act}$ from $G$ to the ring automorphisms of $\mathbb{A}_F =$ `AdeleRing (𝓞 F) F`, each continuous, and compatible with the structure map $F \to \mathbb{A}_F$ in the sense that $D.\mathrm{act}(g)$ applied to the image of $x \in F$ is the image of $g x$. Let $T$ be a set of height-one primes of $\mathcal{O}_F$, and assume that every $w \notin T$ satisfies $\mathrm{ramificationIdx}'$ of $w$ over the contraction $w \cap \mathcal{O}_E$ equal to $1$. Let $U =$ `unitIdelesTrivialOn (𝓞 F) F T` be the subgroup of $\mathbb{A}_F^\times$ consisting of those $x$ whose finite component satisfies, for every $w \notin T$, that both $x_w$ and $(x^{-1})_w$ lie in the valuation ring $\mathcal{O}_w$, and whose infinite part is $1$ and whose $w$-component is $1$ for every $w \in T$. Assume $U$ carries a multiplicative distributive $G$-action whose underlying action on $\mathbb{A}_F^\times$ agrees with the one induced by $D$, namely $g \cdot x = D.\mathrm{unitsAct}(g)(x)$ for all $g$ and $x$. Then for every natural number $n$, the group cohomology of the $\mathbb{Z}$-linear representation of $G$ attached to $U$ in degree $n+1$ is a zero object; that is, $H^{n+1}(G, U) = 0$.
--
--   This is the positive-degree, full-group part of the cohomological triviality of the unit idèles away from $T$ when $F/E$ is unramified outside $T$, a standard ingredient in the class-formation computations for $S$-idèle class groups. It is used by [`M4aHerbrand.subsingleton_tateCohomology_unitIdelesTrivialOn_of_ramificationIdx_eq_one`](thm.html#M4aHerbrand.subsingleton_tateCohomology_unitIdelesTrivialOn_of_ramificationIdx_eq_one), which upgrades it to the vanishing of all Tate cohomology groups in all degrees for all subgroups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_isZero_groupCohomology_unitIdelesTrivialOn_of_ramificationIdx_eq_one.lean

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField IsDedekindDomain M4aHerbrand CategoryTheory

theorem M4aHerbrand.isZero_groupCohomology_unitIdelesTrivialOn_of_ramificationIdx_eq_one
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F) (T : Set (HeightOneSpectrum (𝓞 F)))
    (hunr : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ T → Ideal.ramificationIdx' (w.asIdeal.under (𝓞 E)) w.asIdeal = 1)
    [MulDistribMulAction (F ≃ₐ[E] F) (unitIdelesTrivialOn (𝓞 F) F T)]
    (hactU : ∀ (g : F ≃ₐ[E] F) (x : unitIdelesTrivialOn (𝓞 F) F T),
      ((g • x : unitIdelesTrivialOn (𝓞 F) F T) : (AdeleRing (𝓞 F) F)ˣ) = D.unitsAct g x)
    (n : ℕ) :
    Limits.IsZero (groupCohomology
      (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (unitIdelesTrivialOn (𝓞 F) F T)) (n + 1)) := by sorry
