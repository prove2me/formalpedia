-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_sub_sum_cup_mem_range_d_one_of_mem_ker_d_two_of_topologicalKrullDim_eq_two
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_sub_sum_cup_mem_range_d_one_of_mem_ker_d_two_of_topologicalKrullDim_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/b4b28f0c-d510-53b8-aba6-c5187b452d75
-- title:
--   Degree-two Čech classes on an abelian surface are cup products
-- statement:
--   Let $k$ be an algebraically closed field, $A$ a scheme and $f : A \to \operatorname{Spec} k$ a morphism, equipped with: a relative group law $L$ on $f$, i.e. a system of multiplication, unit and inversion operations on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points over $\operatorname{Spec} k$, natural in $T$ and satisfying the group axioms; the project's bundle `AbelianSchemePropertyBundle` for $f$, which asserts that $f$ is smooth, proper, has connected fibres, and admits a relative group law; and the hypothesis that every fibre $f^{-1}(s)$ has topological Krull dimension $2$. Let $\mathcal K$ be an ordered affine cover of $A$: a finite linearly ordered index set together with affine opens $U_i$ whose supremum is $A$. Čech cochains are taken for the presheaf of modules `OModulePresheaf.unit f`, whose value on an open $U$ is $\Gamma(A,U)$ with its $k$-algebra and restriction structure, so that a cochain in degree $i$ assigns to each index tuple a section over the corresponding intersection. Given $z$ a degree-$2$ cochain with $d z = 0$, the conclusion is that there exist $n \in \mathbb N$ and families $\alpha, \beta : \mathrm{Fin}\,n \to \check C^1$ with $d\alpha_j = 0$ and $d\beta_j = 0$ for all $j$, such that $z - \sum_j \alpha_j \cup \beta_j$ lies in the image of $d : \check C^1 \to \check C^2$, the cup product being the project's pairing of degrees $1$ and $1$ into degree $2$.
--
--   This is the degree-two case of the statement that the Čech cohomology ring of the structure sheaf of an abelian variety is generated in degree one, here in the form needed for an abelian surface and phrased at the level of cochains for a fixed ordered affine cover. It is used in the construction of the graded Čech algebra with its Künneth injectivity and cup-generation properties for such surfaces.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_sub_sum_cup_mem_range_d_one_of_mem_ker_d_two_of_topologicalKrullDim_eq_two.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_sub_sum_cup_mem_range_d_one_of_mem_ker_d_two_of_topologicalKrullDim_eq_two
    (k : Type u) [Field k] [IsAlgClosed k] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hA : AbelianSchemePropertyBundle k f)
    (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = 2)
    (𝒦 : A.OrderedAffineCover)
    (z : (OModulePresheaf.unit f).cochain 𝒦 2) (hz : (OModulePresheaf.unit f).d 𝒦 2 z = 0) :
    ∃ (n : ℕ) (α β : Fin n → (OModulePresheaf.unit f).cochain 𝒦 1),
      (∀ j, (OModulePresheaf.unit f).d 𝒦 1 (α j) = 0) ∧ (∀ j, (OModulePresheaf.unit f).d 𝒦 1 (β j) = 0) ∧
      z - ∑ j, (OModulePresheaf.unit f).cup 𝒦 1 1 2 rfl (α j) (β j) ∈
        LinearMap.range ((OModulePresheaf.unit f).d 𝒦 1) := by sorry
