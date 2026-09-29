-- Prove2me | Theorems.Thm_IharaLemma_map_codRestrict_eq_of_residual
-- name    : IharaLemma.map_codRestrict_eq_of_residual
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/e659b8a1-2c34-5493-bd9f-99cd8b714636
-- title:
--   Saturation and rank force equality of images at a corner
-- statement:
--   Let $\mathcal{O}$ be a discrete valuation ring (a commutative domain which is a discrete valuation ring), let $B$ be a commutative $\mathcal{O}$-algebra, and let $W$ be a $B$-module which is also an $\mathcal{O}$-module with compatible scalar actions, finite and free over $\mathcal{O}$. Fix $e \in B$ and write $eW$ for [`IharaLemma.cornerSubmodule e`](def/IharaLemma_IdempotentSplitting.html#L46), the $B$-submodule of $W$ given by the range of the map $w \mapsto e \cdot w$; it is viewed as an $\mathcal{O}$-submodule by restriction of scalars. Let $V$ be an $\mathcal{O}$-module and $i : V \to W$ an injective $\mathcal{O}$-linear map whose values all lie in $eW$, so that $i$ corestricts to an $\mathcal{O}$-linear map $V \to eW$. Let $\varpi \in \mathcal{O}$ be irreducible and assume $i$ is residually injective in the sense that $i(v) = \varpi \cdot x$ for some $x \in W$ forces $v = \varpi \cdot v_1$ for some $v_1 \in V$. Let $A \subseteq V$ be a saturated $\mathcal{O}$-submodule, i.e. $c \neq 0$ and $c \cdot x \in A$ imply $x \in A$, and let $B_c \subseteq eW$ be an $\mathcal{O}$-submodule containing the image of $A$ under the corestricted map, with $\operatorname{finrank}_{\mathcal{O}} B_c \le \operatorname{finrank}_{\mathcal{O}} A$. Then the image of $A$ in $eW$ equals $B_c$.
--
--   This is the lattice-theoretic step used in level-raising and Ihara-type arguments: a residually injective map of $\mathcal{O}$-lattices carries a saturated submodule onto any submodule of the corner $eW$ that contains it and has no larger rank. It is used in the verification of the Ihara data and Ihara clause at a corner rung of the tower, via [`IharaTower.iharaClauseAt_and_isIharaDataAt_cornerRung`](thm.html#IharaTower.iharaClauseAt_and_isIharaDataAt_cornerRung).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IharaLemma_map_codRestrict_eq_of_residual.lean

import Definitions.Def_IharaLemma_IdempotentSplitting
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IharaLemma.map_codRestrict_eq_of_residual {𝒪 : Type} [CommRing 𝒪] {B : Type}
    [CommRing B] [Algebra 𝒪 B] {W : Type} [AddCommGroup W] [Module B W] [Module 𝒪 W]
    [IsScalarTower 𝒪 B W] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [Module.Finite 𝒪 W] [Module.Free 𝒪 W] {V : Type} [AddCommGroup V] [Module 𝒪 V]
    (i : V →ₗ[𝒪] W) (e : B)
    (hmem : ∀ v : V, i v ∈ (IharaLemma.cornerSubmodule (M := W) e).restrictScalars 𝒪)
    (hi : Function.Injective i) {ϖ : 𝒪} (hϖ : Irreducible ϖ)
    (hres : ∀ (v : V) (x : W), i v = ϖ • x → ∃ v₁ : V, v = ϖ • v₁)
    {A : Submodule 𝒪 V} (hA : ∀ (c : 𝒪) (x : V), c ≠ 0 → c • x ∈ A → x ∈ A)
    {Bc : Submodule 𝒪 ((IharaLemma.cornerSubmodule (M := W) e).restrictScalars 𝒪)}
    (hle : Submodule.map (LinearMap.codRestrict
      ((IharaLemma.cornerSubmodule (M := W) e).restrictScalars 𝒪) i hmem) A ≤ Bc)
    (hrank : Module.finrank 𝒪 Bc ≤ Module.finrank 𝒪 A) :
    Submodule.map (LinearMap.codRestrict
      ((IharaLemma.cornerSubmodule (M := W) e).restrictScalars 𝒪) i hmem) A = Bc := by sorry
