-- Prove2me | Theorems.Thm_NumberField_LevelArith_exists_placesAbove_inl_equiv_infinitePlace
-- name    : NumberField.LevelArith.exists_placesAbove_inl_equiv_infinitePlace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/48fcddb6-1d4d-538d-83ae-9370f091c253
-- title:
--   Archimedean places of a level as Γ_L-orbits
-- statement:
--   Let $K \le L$ be intermediate fields of $\mathbb{Q}$ in $\mathrm{AlgebraicClosure}\,\mathbb{Q}$, both of finite degree over $\mathbb{Q}$, with $hKL : K \le L$, and write $\Gamma = \mathrm{AlgebraicClosure}\,\mathbb{Q} \simeq_{\mathbb{Q}} \mathrm{AlgebraicClosure}\,\mathbb{Q}$, $\Gamma_K = K.\mathrm{fixingSubgroup}$, $\Gamma_L = L.\mathrm{fixingSubgroup}$, and $L' = \mathrm{levelField}\,K\,L\,hKL$ for $L$ regarded as an intermediate field of $K$ in the algebraic closure. Assume $L'$ is normal over $K$, and assume `IsNormalLevel K L`, i.e. $\gamma s \gamma^{-1} \in \Gamma_L$ for all $\gamma \in \Gamma_K$ and $s \in \Gamma_L$. Let $S$ be a finite set of primes, used only to index the component $\mathrm{Sum.inl}\,()$, whose local group is `archimedeanDecomposition` and whose map `extArithLoc` to $\Gamma$ is the inclusion of that subgroup. The assertion is that there is a bijection $e$ between `placesAbove L S (Sum.inl ())`, the set of $\Gamma_L$-orbits on the coset space $\Gamma / \mathrm{archimedeanDecomposition}$, and `NumberField.InfinitePlace` of $L'$, such that for every $\gamma \in \Gamma_K$ and every orbit $x$ one has $e(\gamma \cdot x) = \mathrm{levelGal}\,K\,L\,hKL\,\gamma \cdot e(x)$, where on the left $\gamma$ acts by left translation descended to orbits (`orbitQuotientAction`, legitimate by `IsNormalLevel`) and on the right through the restriction homomorphism $\Gamma_K \to \mathrm{Gal}(L'/K)$ and the Mathlib action of $\mathrm{Gal}(L'/K)$ on infinite places.
--
--   This is the archimedean case of the identification of the local index set of a level with the places of the level field: the abstract $\Gamma_K$-set of $\Gamma_L$-orbits on $\Gamma$ modulo the chosen decomposition group at the real place is matched equivariantly with the infinite places of $L'$. It is used in the additivity/rank computation `finrank_invariants_unitsModP_tensor_add_finrank_invariants_eq` for the $S$-units modulo $p$ over a level, where the archimedean contribution is read off from the infinite places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_exists_placesAbove_inl_equiv_infinitePlace.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith
open scoped Classical NumberField.LevelArith

theorem NumberField.LevelArith.exists_placesAbove_inl_equiv_infinitePlace
    (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L]
    (hKL : K ≤ L) [Normal ↥K ↥(levelField K L hKL)] (hnorm : IsNormalLevel K L) (S : Finset Nat.Primes) :
    ∃ e : placesAbove L S (Sum.inl ()) ≃ NumberField.InfinitePlace ↥(levelField K L hKL),
      ∀ (γ : ↥K.fixingSubgroup) (x : placesAbove L S (Sum.inl ())),
        e ((orbitQuotientAction K L hnorm ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (extArithLoc S (Sum.inl ())).range)).smul γ x) =
          levelGal K L hKL γ • e x := by sorry
