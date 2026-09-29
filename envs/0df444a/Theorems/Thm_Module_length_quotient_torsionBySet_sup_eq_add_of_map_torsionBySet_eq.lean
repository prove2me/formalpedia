-- Prove2me | Theorems.Thm_Module_length_quotient_torsionBySet_sup_eq_add_of_map_torsionBySet_eq
-- name    : Module.length_quotient_torsionBySet_sup_eq_add_of_map_torsionBySet_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/ab91d3dd-aa48-5c0d-982b-ad222c8fa819
-- title:
--   Congruence module length growth along an adjoint pair
-- statement:
--   Let $\mathcal{O}$ be a principal ideal domain, and let $T$ and $T'$ be commutative $\mathcal{O}$-algebras equipped with $\mathcal{O}$-algebra maps $\pi_T : T \to \mathcal{O}$ and $\pi_{T'} : T' \to \mathcal{O}$; write $\wp = \ker \pi_T$ and $\wp' = \ker \pi_{T'}$, and assume the ideals $\pi_T(\mathrm{Ann}\,\wp)$ and $\pi_{T'}(\mathrm{Ann}\,\wp')$ of $\mathcal{O}$ are both nonzero. Let $M$ be a $T$-module which is also an $\mathcal{O}$-module compatibly (scalar tower), finite and free over $\mathcal{O}$, and let $B : M \times M \to \mathcal{O}$ be an $\mathcal{O}$-bilinear form satisfying $B(tm,n) = B(m,tn)$ for all $t \in T$ and such that $m \mapsto B(m,-)$ is a bijection $M \to \mathrm{Hom}_{\mathcal{O}}(M,\mathcal{O})$; let $(M',B')$ be such data over $T'$. Suppose given $\mathcal{O}$-linear maps $i : M \to M'$ and $j : M' \to M$ adjoint for the two forms, $B(j m', m) = B'(m', i m)$, and $\Delta \in T$ with $j \circ i = \Delta \cdot {-}$ on $M$ and $\pi_T(\Delta) \neq 0$. Here $M[\wp]$ denotes the submodule of elements of $M$ annihilated by every element of $\wp$, and likewise for $M[\mathrm{Ann}\,\wp]$, $M'[\wp']$, $M'[\mathrm{Ann}\,\wp']$. Assume finally that $i$ carries $M[\wp]$ exactly onto $M'[\wp']$. Then $M'[\wp']$ and $M[\wp]$ have the same $\mathcal{O}$-rank $d$, and, as elements of $\mathbb{N} \cup \{\infty\}$,
--   $$\mathrm{length}_{\mathcal{O}}\, M'/(M'[\wp'] + M'[\mathrm{Ann}\,\wp']) = \mathrm{length}_{\mathcal{O}}\, M/(M[\wp] + M[\mathrm{Ann}\,\wp]) + d \cdot \mathrm{length}_{\mathcal{O}}\, \mathcal{O}/\pi_T(\Delta)\mathcal{O}.$$
--
--   This is the commutative-algebra bookkeeping for one step of a level-change induction: it computes how the length of the congruence-type quotient $M/(M[\wp]+M[\mathrm{Ann}\,\wp])$ of a self-dual Hecke module grows when one passes along a pair of adjoint degeneracy-type maps whose composite is multiplication by $\Delta$, the hypothesis that $i$ carries $M[\wp]$ onto $M'[\wp']$ being what Ihara-type results supply classically. It is used by [`AlgHom.bijective_and_free_of_length_le_of_levelChange`](thm.html#AlgHom.bijective_and_free_of_length_le_of_levelChange), which converts a length inequality at a changed level into an isomorphism and freeness statement.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_length_quotient_torsionBySet_sup_eq_add_of_map_torsionBySet_eq.lean

import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dual.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w x

theorem Module.length_quotient_torsionBySet_sup_eq_add_of_map_torsionBySet_eq
    {𝒪 : Type u} {T T' : Type w} [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
    [CommRing T] [Algebra 𝒪 T] [CommRing T'] [Algebra 𝒪 T']
    (πT : T →ₐ[𝒪] 𝒪) (hη : (RingHom.ker πT).annihilator.map πT ≠ ⊥)
    (πT' : T' →ₐ[𝒪] 𝒪) (hη' : (RingHom.ker πT').annihilator.map πT' ≠ ⊥)
    (M : Type x) [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
    [Module.Finite 𝒪 M] [Module.Free 𝒪 M]
    (B : M →ₗ[𝒪] M →ₗ[𝒪] 𝒪) (hB : ∀ (t : T) (m n : M), B (t • m) n = B m (t • n))
    (hBb : Function.Bijective B)
    (M' : Type x) [AddCommGroup M'] [Module T' M'] [Module 𝒪 M'] [IsScalarTower 𝒪 T' M']
    [Module.Finite 𝒪 M'] [Module.Free 𝒪 M']
    (B' : M' →ₗ[𝒪] M' →ₗ[𝒪] 𝒪) (hB' : ∀ (t : T') (m n : M'), B' (t • m) n = B' m (t • n))
    (hBb' : Function.Bijective B')
    (i : M →ₗ[𝒪] M') (j : M' →ₗ[𝒪] M) (hadj : ∀ (m' : M') (m : M), B (j m') m = B' m' (i m))
    (Δ : T) (hji : ∀ m : M, j (i m) = Δ • m) (hΔ : πT Δ ≠ 0)
    (h℘ : Submodule.map i ((Submodule.torsionBySet T M ↑(RingHom.ker πT)).restrictScalars 𝒪) =
      (Submodule.torsionBySet T' M' ↑(RingHom.ker πT')).restrictScalars 𝒪) :
    Module.finrank 𝒪 (Submodule.torsionBySet T' M' ↑(RingHom.ker πT')) =
        Module.finrank 𝒪 (Submodule.torsionBySet T M ↑(RingHom.ker πT)) ∧
      Module.length 𝒪 (M' ⧸ (Submodule.torsionBySet T' M' ↑(RingHom.ker πT') ⊔
          Submodule.torsionBySet T' M' ↑(RingHom.ker πT').annihilator)) =
        Module.length 𝒪 (M ⧸ (Submodule.torsionBySet T M ↑(RingHom.ker πT) ⊔
          Submodule.torsionBySet T M ↑(RingHom.ker πT).annihilator)) +
        (Module.finrank 𝒪 (Submodule.torsionBySet T M ↑(RingHom.ker πT)) : ℕ∞) *
          Module.length 𝒪 (𝒪 ⧸ Ideal.span {πT Δ}) := by sorry
