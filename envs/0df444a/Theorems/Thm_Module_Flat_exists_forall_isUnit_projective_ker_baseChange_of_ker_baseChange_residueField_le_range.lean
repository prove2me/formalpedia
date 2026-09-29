-- Prove2me | Theorems.Thm_Module_Flat_exists_forall_isUnit_projective_ker_baseChange_of_ker_baseChange_residueField_le_range
-- name    : Module.Flat.exists_forall_isUnit_projective_ker_baseChange_of_ker_baseChange_residueField_le_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/e69f3b7c-aed1-5e27-8007-ccc2efdd9584
-- title:
--   Universal acyclicity and projectivity near a good fibre
-- statement:
--   Let $R$ be a commutative Noetherian ring and let $C : \mathbb{N} \to \mathrm{Type}$ be a family of $R$-modules, each flat, equipped with maps $d_i : C_i \to C_{i+1}$ satisfying $d_{i+1} \circ d_i = 0$ for all $i$; assume there is $n$ with $C_i$ subsingleton for all $i \ge n$, that $\ker(d_0)$ is a finite $R$-module, and that for every $i$ the cohomology $\ker(d_{i+1})$ modulo the preimage of $\operatorname{range}(d_i)$ along the inclusion $\ker(d_{i+1}) \hookrightarrow C_{i+1}$ is a finite $R$-module. Let $\mathfrak p$ be a prime of $R$ and suppose the complex becomes exact in positive degrees after base change to the residue field $\kappa(\mathfrak p)$, in the sense that $\ker(d_{i+1} \otimes \kappa(\mathfrak p)) \le \operatorname{range}(d_i \otimes \kappa(\mathfrak p))$ for all $i$. Then there exists $g \in R$ with $g \notin \mathfrak p$ such that for every $R$-algebra $A$ (in the same universe) in which the image of $g$ is a unit: $\ker(d_0 \otimes A)$ is a finite projective $A$-module; $\ker(d_{i+1} \otimes A) \le \operatorname{range}(d_i \otimes A)$ for all $i$; the comparison map [`TwoChartCech.kerBaseChangeHom (d 0) A`](def/AlgebraicGeometry_TwoChartCech.html#L123), obtained by base changing the inclusion $\ker(d_0) \hookrightarrow C_0$ to $A$ and corestricting it to $\ker(d_0 \otimes A)$, is bijective; and for every prime $\mathfrak q$ of $A$ the rank at the stalk of $\ker(d_0 \otimes A)$ at $\mathfrak q$ equals $\dim_{\kappa(\mathfrak p)} \ker(d_0 \otimes \kappa(\mathfrak p))$.
--
--   This is the cohomology-and-base-change statement in the form needed downstream: a bounded complex of flat modules with finitely generated cohomology over a Noetherian base, acyclic in positive degrees on the fibre at $\mathfrak p$, is universally acyclic with finite projective degree-zero kernel of constant rank over a basic open neighbourhood $D(g)$ of $\mathfrak p$, and the formation of that kernel commutes with arbitrary base change inverting $g$. It is used in the construction of points of the Hilbert functor, in [`AlgebraicGeometry.HilbertFunctor.exists_point_I_eq_span_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation`](thm.html#AlgebraicGeometry.HilbertFunctor.exists_point_I_eq_span_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_Flat_exists_forall_isUnit_projective_ker_baseChange_of_ker_baseChange_residueField_le_range.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open TensorProduct

theorem Module.Flat.exists_forall_isUnit_projective_ker_baseChange_of_ker_baseChange_residueField_le_range
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hbd : ∀ i, n ≤ i → Subsingleton (C i))
    (hfin0 : Module.Finite R (LinearMap.ker (d 0)))
    (hfin : ∀ i, Module.Finite R
      (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype))
    (𝔭 : PrimeSpectrum R)
    (hfib : ∀ i : ℕ,
      LinearMap.ker ((d (i + 1)).baseChange 𝔭.asIdeal.ResidueField) ≤
        LinearMap.range ((d i).baseChange 𝔭.asIdeal.ResidueField)) :
    ∃ g : R, g ∉ 𝔭.asIdeal ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A], IsUnit (algebraMap R A g) →
        Module.Finite A (LinearMap.ker ((d 0).baseChange A)) ∧
        Module.Projective A (LinearMap.ker ((d 0).baseChange A)) ∧
        (∀ i : ℕ, LinearMap.ker ((d (i + 1)).baseChange A) ≤ LinearMap.range ((d i).baseChange A)) ∧
        Function.Bijective (TwoChartCech.kerBaseChangeHom (d 0) A) ∧
        (∀ 𝔮 : PrimeSpectrum A,
          Module.rankAtStalk (LinearMap.ker ((d 0).baseChange A)) 𝔮 =
            Module.finrank 𝔭.asIdeal.ResidueField (LinearMap.ker ((d 0).baseChange 𝔭.asIdeal.ResidueField))) := by sorry
