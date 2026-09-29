-- Prove2me | Theorems.Thm_Module_Flat_exists_forall_isUnit_ker_baseChange_le_range_of_ker_baseChange_residueField_le_range
-- name    : Module.Flat.exists_forall_isUnit_ker_baseChange_le_range_of_ker_baseChange_residueField_le_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/78b2353f-7a87-5883-814e-87809458d424
-- title:
--   Fibrewise exactness of a bounded flat complex spreads out
-- statement:
--   Let $R$ be a commutative Noetherian ring and let $C : \mathbb{N} \to \mathrm{Type}$ be a family of $R$-modules, each flat over $R$, equipped with $R$-linear maps $d_i : C_i \to C_{i+1}$ satisfying $d_{i+1} \circ d_i = 0$ for all $i$, so that $(C,d)$ is a cochain complex of flat modules. Assume there is $n \in \mathbb{N}$ with $C_i$ a subsingleton (i.e. zero) for all $i \ge n$, and that for every $i$ the cohomology module $\ker(d_{i+1}) / (\operatorname{im}(d_i) \cap \ker(d_{i+1}))$ — formed as the quotient of $\ker(d_{i+1}) \subseteq C_{i+1}$ by the preimage of $\operatorname{im}(d_i)$ under the inclusion of $\ker(d_{i+1})$ — is a finite (finitely generated) $R$-module. Let $\mathfrak{p}$ be a prime of $R$ and suppose the fibre complex over the residue field $\kappa(\mathfrak{p})$ is exact, in the sense that $\ker(d_{i+1} \otimes \kappa(\mathfrak{p})) \le \operatorname{im}(d_i \otimes \kappa(\mathfrak{p}))$ for all $i$, where $\otimes$ denotes base change of linear maps. The conclusion asserts the existence of $g \in R$ with $g \notin \mathfrak{p}$ such that for every commutative $R$-algebra $S$ which is a localisation of $R$ away from $g$, and every $i$, one has $\ker(d_{i+1} \otimes S) \le \operatorname{im}(d_i \otimes S)$ inside $S \otimes_R C_{i+1}$.
--
--   This is the spreading-out half of the standard cohomology-and-base-change package: exactness of a bounded complex of flat modules with finitely generated cohomology on the fibre at one point persists over a basic open neighbourhood of that point. It feeds the projectivity statement [`Module.Flat.exists_forall_isUnit_projective_ker_baseChange_of_ker_baseChange_residueField_le_range`](thm.html#Module.Flat.exists_forall_isUnit_projective_ker_baseChange_of_ker_baseChange_residueField_le_range) in the two-chart Čech development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_Flat_exists_forall_isUnit_ker_baseChange_le_range_of_ker_baseChange_residueField_le_range.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open TensorProduct

theorem Module.Flat.exists_forall_isUnit_ker_baseChange_le_range_of_ker_baseChange_residueField_le_range
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hbd : ∀ i, n ≤ i → Subsingleton (C i))
    (hfin : ∀ i, Module.Finite R
      (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype))
    (𝔭 : PrimeSpectrum R)
    (hfib : ∀ i : ℕ,
      LinearMap.ker ((d (i + 1)).baseChange 𝔭.asIdeal.ResidueField) ≤
        LinearMap.range ((d i).baseChange 𝔭.asIdeal.ResidueField)) :
    ∃ g : R, g ∉ 𝔭.asIdeal ∧
      ∀ (S : Type u) [CommRing S] [Algebra R S] [IsLocalization.Away g S],
        ∀ i : ℕ, LinearMap.ker ((d (i + 1)).baseChange S) ≤ LinearMap.range ((d i).baseChange S) := by sorry
