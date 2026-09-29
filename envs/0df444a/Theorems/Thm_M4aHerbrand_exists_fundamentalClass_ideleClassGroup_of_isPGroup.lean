-- Prove2me | Theorems.Thm_M4aHerbrand_exists_fundamentalClass_ideleClassGroup_of_isPGroup
-- name    : M4aHerbrand.exists_fundamentalClass_ideleClassGroup_of_isPGroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/63837ab0-eb8e-570c-8ec5-b5d67b1624dd
-- title:
--   Fundamental class in H² of the idèle class group for p-extensions
-- statement:
--   Let $E \subseteq F$ be number fields with $F/E$ Galois, write $G = F \simeq_{\mathrm{alg}[E]} F$ for its Galois group, let $p$ be a prime and assume `IsPGroup p G`, i.e. $G$ is a $p$-group. Let $D$ be an `IdeleGaloisDescent (𝓞 F) E F`: a monoid homomorphism from $G$ to the ring automorphisms of the adèle ring $\mathbb{A}_F$ of $F$ (formed relative to $\mathcal{O}_F$), each automorphism continuous, and compatible with the structure map $F \to \mathbb{A}_F$ in the sense that $D(g)$ applied to the image of $x \in F$ is the image of $g x$. Let $C_F = \mathbb{A}_F^\times / \mathrm{principalIdeles}$, the quotient of the unit group of the adèle ring by the image of $F^\times$, be equipped with a multiplicative distributive $G$-action which agrees with the one induced by $D$ on units and passed to the quotient (`D.classAct`). The conclusion asserts the existence of a class $u \in H^2(G, C_F)$, cohomology of the $\mathbb{Z}$-linear representation `Rep.ofMulDistribMulAction`, such that, for every subgroup $S \le G$: $H^1(S, C_F)$ (cohomology of the restricted representation) is a zero object; for every such $S$ equipped with a `Fintype` structure, $\#H^2(S, C_F) = \#S$; and the restriction of $u$ to $H^2(S, C_F)$, via `groupCohomology.map` along the inclusion $S \hookrightarrow G$ with the identity on the restricted representation, generates $H^2(S, C_F)$ as a $\mathbb{Z}$-module.
--
--   This is the existence of the global fundamental class for a Galois extension of number fields whose group is a $p$-group, in the form used to verify the axioms of class formations: vanishing of $H^1$ and cyclicity of $H^2$ of order $\#S$ with generator the restriction of a single global class. It feeds the comparison of the global fundamental class with the local ones at residue characteristic different from $2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_exists_fundamentalClass_ideleClassGroup_of_isPGroup.lean

import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField M4aHerbrand CategoryTheory

theorem M4aHerbrand.exists_fundamentalClass_ideleClassGroup_of_isPGroup
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p (F ≃ₐ[E] F))
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c) :
    ∃ u : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2,
      (∀ S : Subgroup (F ≃ₐ[E] F), Limits.IsZero
        (groupCohomology (Rep.res S.subtype
          (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 1)) ∧
      (∀ (S : Subgroup (F ≃ₐ[E] F)) [Fintype S], Nat.card
        (groupCohomology (Rep.res S.subtype
          (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) = Fintype.card S) ∧
      (∀ S : Subgroup (F ≃ₐ[E] F), Submodule.span ℤ
        {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype
          (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom u} = ⊤) := by sorry
