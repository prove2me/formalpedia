-- Prove2me | Theorems.Thm_MeasureTheory_Measure_exists_isHaarMeasure_subgroup_units_map_val_eq_withDensity_of_abs_det_eq
-- name    : MeasureTheory.Measure.exists_isHaarMeasure_subgroup_units_map_val_eq_withDensity_of_abs_det_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/94e7fafa-d868-5690-958c-e00cbf41d461
-- title:
--   Haar measure |χ|⁻¹ dx on units of a real subalgebra
-- statement:
--   Let $M$ be a finite-dimensional associative unital $\mathbb{R}$-algebra which is at the same time a Hausdorff topological ring with continuous scalar multiplication, equipped with its Borel $\sigma$-algebra. Let $A$ be an $\mathbb{R}$-subalgebra of $M$ and $\Gamma$ a subgroup of $M^\times$ which is assumed to consist exactly of those units $g$ with $g \in A$, i.e. $g \in \Gamma \iff (g : M) \in A$. Let $e : \mathrm{Fin}\,n \to M$ be $\mathbb{R}$-linearly independent with $\mathbb{R}$-span equal to the underlying submodule of $A$, so $e$ is a basis of $A$. Let $\chi : M \to \mathbb{R}$ be a continuous multiplicative map (a monoid homomorphism for multiplication), and assume that for every $g \in \Gamma$ there are real $n \times n$ matrices $P$ and $Q$ with $g\,e_j = \sum_i P_{ij} e_i$ and $e_j\,g = \sum_i Q_{ij} e_i$ for all $j$, and $|\det P| = |\det Q| = |\chi(g)|$. Then, for the Borel $\sigma$-algebra on $\Gamma$, there exists a measure $\tau$ on $\Gamma$ which is a Haar measure (left invariant, and the further properties packaged in `IsHaarMeasure`) and also right invariant, such that the pushforward of $\tau$ along $t \mapsto (t : M)$ equals the pushforward of Lebesgue measure on $\mathbb{R}^n$ along $c \mapsto \sum_i c_i e_i$, taken with density $x \mapsto (\mathrm{ENNReal.ofReal}\,|\chi(x)|)^{-1}$.
--
--   This is the classical description $d^\times x = |N(x)|^{-1}\,dx$ of a Haar measure on the unit group of a finite-dimensional real algebra, stated for a subalgebra $A$ sitting inside an ambient topological algebra $M$ so that $\Gamma$ carries the topology induced from $M^\times$, with the reduced norm replaced by an abstract multiplicative map $\chi$ whose absolute value computes the Jacobians of left and right translation. It supplies the archimedean local measure, together with its two-sided invariance, in the construction of measures on twisted centralisers used for automorphic forms on quaternion algebras.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_Measure_exists_isHaarMeasure_subgroup_units_map_val_eq_withDensity_of_abs_det_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.Measure.exists_isHaarMeasure_subgroup_units_map_val_eq_withDensity_of_abs_det_eq
    {M : Type*} [Ring M] [Algebra ℝ M] [FiniteDimensional ℝ M]
    [TopologicalSpace M] [IsTopologicalRing M] [ContinuousSMul ℝ M] [T2Space M]
    [MeasurableSpace M] [BorelSpace M]
    (A : Subalgebra ℝ M) (Γ : Subgroup Mˣ) (hΓ : ∀ g : Mˣ, g ∈ Γ ↔ (g : M) ∈ A)
    (n : ℕ) (e : Fin n → M) (hli : LinearIndependent ℝ e)
    (hsp : Submodule.span ℝ (Set.range e) = Subalgebra.toSubmodule A)
    (χ : M →* ℝ) (hχ : Continuous χ)
    (hleft : ∀ g : Mˣ, g ∈ Γ → ∃ P : Matrix (Fin n) (Fin n) ℝ,
      (∀ j, (g : M) * e j = ∑ i, P i j • e i) ∧ |P.det| = |χ g|)
    (hright : ∀ g : Mˣ, g ∈ Γ → ∃ Q : Matrix (Fin n) (Fin n) ℝ,
      (∀ j, e j * (g : M) = ∑ i, Q i j • e i) ∧ |Q.det| = |χ g|) :
    letI : MeasurableSpace Γ := borel Γ
    ∃ τ : Measure Γ, τ.IsHaarMeasure ∧ τ.IsMulRightInvariant ∧
      Measure.map (fun t : Γ => ((t : Mˣ) : M)) τ =
        (Measure.map (fun c : Fin n → ℝ => ∑ i, c i • e i) volume).withDensity
          fun x => (ENNReal.ofReal |χ x|)⁻¹ := by sorry
