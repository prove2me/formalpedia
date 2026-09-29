-- Prove2me | Theorems.Thm_IharaTower_map_torsionBySet_eq_of_forall_eq_smul_of_finrank_le
-- name    : IharaTower.map_torsionBySet_eq_of_forall_eq_smul_of_finrank_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/27d8399f-7c59-5518-a779-a5e43a5ba8a4
-- title:
--   Saturation and rank force a residually injective map onto eigen-submodules
-- statement:
--   Let $\mathcal{O}$ be a discrete valuation ring (a commutative domain which is a discrete valuation ring), let $T$ and $T'$ be commutative $\mathcal{O}$-algebras, let $M$ be an abelian group carrying compatible $T$- and $\mathcal{O}$-module structures ($\mathcal{O}$ acting through $T$) which is finite and free as an $\mathcal{O}$-module, and likewise let $M'$ be a module over $T'$ and over $\mathcal{O}$, finite and free over $\mathcal{O}$. Let $i : M \to M'$ be $\mathcal{O}$-linear, let $\pi_T : T \to \mathcal{O}$ and $\pi_{T'} : T' \to \mathcal{O}$ be $\mathcal{O}$-algebra homomorphisms, and let $\varpi \in \mathcal{O}$ be irreducible. Write $A \subseteq M$ for the $\mathcal{O}$-submodule of those $m$ with $t \cdot m = 0$ for all $t \in \ker \pi_T$, and $B \subseteq M'$ for the $\mathcal{O}$-submodule of those $m'$ with $t' \cdot m' = 0$ for all $t' \in \ker \pi_{T'}$. Assume: (i) for all $v \in M$ and $x \in M'$, if $i(v) = \varpi x$ then $v \in \varpi M$; (ii) $i(A) \subseteq B$; (iii) $\operatorname{rank}_{\mathcal{O}} B \le \operatorname{rank}_{\mathcal{O}} A$ (finite ranks over $\mathcal{O}$). Then $i$ is injective and $i(A) = B$.
--
--   This is the elementary passage from Ihara's lemma modulo a uniformiser to the assertion that a level-raising map identifies the eigen-submodule cut out by $\ker\pi_T$ at the old level with the one cut out by $\ker\pi_{T'}$ at the new level, the modules $M$, $M'$ being localised cohomology and $i$ a combination of degeneracy maps. It is used in the construction of the rungs of the Hecke-algebra tower, at primes dividing the level to first order and at primes not dividing it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IharaTower_map_torsionBySet_eq_of_forall_eq_smul_of_finrank_le.lean

import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IharaTower.map_torsionBySet_eq_of_forall_eq_smul_of_finrank_le
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {T : Type} [CommRing T] [Algebra 𝒪 T] {T' : Type} [CommRing T'] [Algebra 𝒪 T']
    {M : Type} [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
    [Module.Finite 𝒪 M] [Module.Free 𝒪 M]
    {M' : Type} [AddCommGroup M'] [Module T' M'] [Module 𝒪 M'] [IsScalarTower 𝒪 T' M']
    [Module.Finite 𝒪 M'] [Module.Free 𝒪 M']
    (i : M →ₗ[𝒪] M') (πT : T →ₐ[𝒪] 𝒪) (πT' : T' →ₐ[𝒪] 𝒪)
    {ϖ : 𝒪} (hϖ : Irreducible ϖ)
    (hres : ∀ (v : M) (x : M'), i v = ϖ • x → ∃ v₁ : M, v = ϖ • v₁)
    (hincl : Submodule.map i ((Submodule.torsionBySet T M ↑(RingHom.ker πT)).restrictScalars 𝒪) ≤
      (Submodule.torsionBySet T' M' ↑(RingHom.ker πT')).restrictScalars 𝒪)
    (hrank : Module.finrank 𝒪
        ((Submodule.torsionBySet T' M' ↑(RingHom.ker πT')).restrictScalars 𝒪) ≤
      Module.finrank 𝒪 ((Submodule.torsionBySet T M ↑(RingHom.ker πT)).restrictScalars 𝒪)) :
    Function.Injective i ∧
    Submodule.map i ((Submodule.torsionBySet T M ↑(RingHom.ker πT)).restrictScalars 𝒪) =
      (Submodule.torsionBySet T' M' ↑(RingHom.ker πT')).restrictScalars 𝒪 := by sorry
