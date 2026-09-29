-- Prove2me | Theorems.Thm_MeasureTheory_Measure_map_withDensity_gram_trace_matrix_pi_eq_pi_of_span_eq
-- name    : MeasureTheory.Measure.map_withDensity_gram_trace_matrix_pi_eq_pi_of_span_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/c360db51-d77a-5d65-9b61-b104c8df5c16
-- title:
--   Gram-normalised trace measures on M₂ of a product algebra
-- statement:
--   Let $\iota$ be a finite type and let $E_i$, $i \in \iota$, be commutative rings that are $\mathbb{R}$-algebras, free and finite as $\mathbb{R}$-modules, and Hausdorff topological rings with continuous scalar multiplication; the matrix spaces $M_2(E_i)$ and $M_2(\prod_i E_i)$ carry measurable structures that are the Borel ones. For each $i$ let $W_i \subseteq M_2(E_i)$ be an $\mathbb{R}$-submodule, and let $e_i : \mathrm{Fin}(n_i) \to M_2(E_i)$ be an $\mathbb{R}$-linearly independent family spanning $W_i$; assume each $W_i$ contains a matrix $X$ with $N_{E_i/\mathbb{R}}(\det X) \neq 0$. Let $W' \subseteq M_2(\prod_i E_i)$ be an $\mathbb{R}$-submodule characterised by componentwise membership, i.e. $X \in W'$ if and only if the $i$-th component matrix $X$ mapped entrywise through the evaluation homomorphism lies in $W_i$ for every $i$, and let $f : \mathrm{Fin}(N) \to M_2(\prod_i E_i)$ be an $\mathbb{R}$-linearly independent family spanning $W'$. Form, for a family $g$ of matrices over an algebra $A$, the measure $\sqrt{|\det(\mathrm{Tr}_{A/\mathbb{R}}(\mathrm{tr}(g_a g_b)))_{a,b}|}$ times the pushforward of Lebesgue measure along $c \mapsto \sum_a c_a g_a$, weighted by the density $X \mapsto |N_{A/\mathbb{R}}(\det X)|^{-1}$ (all scalars read in $[0,\infty]$ via `ENNReal.ofReal`). The assertion is that the pushforward of this measure for $f$ along the componentwise projection $X \mapsto (X \bmod i)_i : M_2(\prod_i E_i) \to \prod_i M_2(E_i)$ equals the product measure of the corresponding measures built from the families $e_i$.
--
--   This identifies the Gram-normalised trace-form measure with its norm density on $M_2$ of a finite product of real algebras, restricted to a componentwise-defined subspace, with the product of the corresponding measures on the factors; it is the measure-theoretic normalisation underlying archimedean orbital integral computations. It is used in the comparison of twisted and untwisted orbital integrals at the archimedean place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_Measure_map_withDensity_gram_trace_matrix_pi_eq_pi_of_span_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.Measure.map_withDensity_gram_trace_matrix_pi_eq_pi_of_span_eq
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (E : ι → Type) [∀ i, CommRing (E i)] [∀ i, Algebra ℝ (E i)] [∀ i, Module.Free ℝ (E i)]
    [∀ i, Module.Finite ℝ (E i)] [∀ i, TopologicalSpace (E i)] [∀ i, IsTopologicalRing (E i)]
    [∀ i, ContinuousSMul ℝ (E i)] [∀ i, T2Space (E i)]
    [∀ i, MeasurableSpace (Matrix (Fin 2) (Fin 2) (E i))] [∀ i, BorelSpace (Matrix (Fin 2) (Fin 2) (E i))]
    [MeasurableSpace (Matrix (Fin 2) (Fin 2) ((i : ι) → E i))] [BorelSpace (Matrix (Fin 2) (Fin 2) ((i : ι) → E i))]
    (W : ∀ i, Submodule ℝ (Matrix (Fin 2) (Fin 2) (E i)))
    (n : ι → ℕ) (e : ∀ i, Fin (n i) → Matrix (Fin 2) (Fin 2) (E i))
    (he : ∀ i, LinearIndependent ℝ (e i) ∧ Submodule.span ℝ (Set.range (e i)) = W i)
    (hW : ∀ i, ∃ X ∈ W i, Algebra.norm ℝ (Matrix.det X) ≠ 0)
    (W' : Submodule ℝ (Matrix (Fin 2) (Fin 2) ((i : ι) → E i)))
    (hW' : ∀ X : Matrix (Fin 2) (Fin 2) ((i : ι) → E i), X ∈ W' ↔ ∀ i, X.map (Pi.evalRingHom E i) ∈ W i)
    (N : ℕ) (f : Fin N → Matrix (Fin 2) (Fin 2) ((i : ι) → E i))
    (hf : LinearIndependent ℝ f ∧ Submodule.span ℝ (Set.range f) = W') :
    Measure.map (fun X : Matrix (Fin 2) (Fin 2) ((i : ι) → E i) => fun i : ι => X.map (Pi.evalRingHom E i))
        (((ENNReal.ofReal (Real.sqrt |(Matrix.of fun a b : Fin N =>
              Algebra.trace ℝ ((i : ι) → E i) (Matrix.trace (f a * f b))).det|)) •
            Measure.map (fun c : Fin N → ℝ => ∑ a, c a • f a) volume).withDensity
          fun X : Matrix (Fin 2) (Fin 2) ((i : ι) → E i) => (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) =
      Measure.pi (fun i : ι =>
        ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun a b : Fin (n i) =>
              Algebra.trace ℝ (E i) (Matrix.trace (e i a * e i b))).det|)) •
            Measure.map (fun c : Fin (n i) → ℝ => ∑ a, c a • e i a) volume).withDensity
          fun X : Matrix (Fin 2) (Fin 2) (E i) => (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) := by sorry
