-- Prove2me | Theorems.Thm_HeckeIntegralSeam_exists_isHeckeCosetSystem_and_isHeckeCosetSystem_mul_inv_of_conj_eq
-- name    : HeckeIntegralSeam.exists_isHeckeCosetSystem_and_isHeckeCosetSystem_mul_inv_of_conj_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/7b783ace-b520-5ae1-b7ca-4ad19b25deba
-- title:
--   Common transversal for UgU and its adjoint system
-- statement:
--   Let $G$ be a group, $U \le G$ a subgroup, $g, w, z \in G$, $\iota$ an index type and $\mathrm{reps} : \iota \to G$ a family satisfying `IsHeckeCosetSystem U g reps`, that is: each $\mathrm{reps}\,i$ lies in the double coset $U\{g\}U$; every $x \in U\{g\}U$ has some index $i$ with $xU = (\mathrm{reps}\,i)U$ as elements of $G \,⧸\, U$; and the map $i \mapsto (\mathrm{reps}\,i)U$ is injective. Assume further $w \in U$, that $z$ lies in the centre of $G$, and that $w g w^{-1} = z g^{-1}$. The conclusion is the existence of a family $\varepsilon : \iota \to G$ such that: $\varepsilon$ is again such a system for $U$ and $g$ (each $\varepsilon\,i \in U\{g\}U$, the cosets $(\varepsilon\,i)U$ exhaust the left cosets meeting $U\{g\}U$, and $i \mapsto (\varepsilon\,i)U$ is injective); $(\varepsilon\,i)U = (\mathrm{reps}\,i)U$ for every $i$, so $\varepsilon$ represents the same cosets as $\mathrm{reps}$; and the family $i \mapsto z(\varepsilon\,i)^{-1}$ is once more such a system for $U$ and $g$.
--
--   This is the group-theoretic lemma underlying the self-adjointness of Hecke operators attached to a double coset $UgU$ satisfying $UgU = z\,Ug^{-1}U$ with $z$ central, in the form of a system of left-coset representatives that is simultaneously adapted to the inverted double coset (compare Shimura's treatment of Hecke rings). It feeds the results on Hecke coset eigenfunctions of right convolution at level one and at principal level, namely [`AutomorphicForm.isHeckeCosetEigenfunctionAt_rightConv_of_isBiInvariantUnder_levelOne_of_not_dvd`](thm.html#AutomorphicForm.isHeckeCosetEigenfunctionAt_rightConv_of_isBiInvariantUnder_levelOne_of_not_dvd) and [`AutomorphicForm.isHeckeCosetEigenfunctionAt_rightConv_of_isBiInvariantUnder_principalLevel_of_not_dvd`](thm.html#AutomorphicForm.isHeckeCosetEigenfunctionAt_rightConv_of_isBiInvariantUnder_principalLevel_of_not_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeIntegralSeam_exists_isHeckeCosetSystem_and_isHeckeCosetSystem_mul_inv_of_conj_eq.lean

import Mathlib
import Definitions.Def_LocalLanglands_HeckeCosetSystem

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem HeckeIntegralSeam.exists_isHeckeCosetSystem_and_isHeckeCosetSystem_mul_inv_of_conj_eq
    {G : Type*} [Group G] {U : Subgroup G} {g w z : G} {ι : Type*} {reps : ι → G}
    (hsys : HeckeIntegralSeam.IsHeckeCosetSystem U g reps) (hw : w ∈ U)
    (hz : z ∈ Subgroup.center G) (hconj : w * g * w⁻¹ = z * g⁻¹) :
    ∃ ε : ι → G, HeckeIntegralSeam.IsHeckeCosetSystem U g ε ∧
      (∀ i, (QuotientGroup.mk (ε i) : G ⧸ U) = QuotientGroup.mk (reps i)) ∧
      HeckeIntegralSeam.IsHeckeCosetSystem U g (fun i => z * (ε i)⁻¹) := by sorry
