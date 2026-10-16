-- Prove2me | Theorems.Thm_InfFisher_Linear_lemma_5
-- name    : InfFisher.Linear.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:05:34.408989+00:00
-- url     : https://prove2.me/theorems/fbcc7c92-516c-4e2d-ad4d-ac789e044394
-- title:
--   Lemma 5, p. 14 — unique ordered equilibrium partition
-- statement:
--   Under Assumption 1, let $B_i>0$ for every buyer: valuations are normalized nonnegative lines on $[0,1]$ with strictly decreasing intercepts. There are unique ordered breakpoints $0=a_0<a_1<\cdots<a_n=1$ giving the pure equilibrium allocation in which buyer $i$ receives $[a_{i-1},a_i]$. Every equilibrium allocation agrees with this one almost everywhere, and its price is the maximum scaled valuation:
--
--   $$p(\theta)=\max_i\beta_i v_i(\theta)\quad\text{a.e.},\qquad \beta_i=\frac{B_i}{\langle v_i,x_i\rangle}.$$
--
--   On the interior of buyer $i$'s interval, its scaled valuation strictly exceeds every other buyer's. This states the $n$ distinct linear price pieces and the uniqueness of the equilibrium allocation used for Lemma 7.
--
--   **Formalization Note** The paper numbers buyers from one; Lean buyer $i$ receives $[a_i,a_{i+1}]$. Equality of allocations and prices is almost everywhere.
-- source:
--   Gao & Kroer, Infinite-Dimensional Fisher Markets and Tractable Fair Division, arXiv:2010.03025v5, Assumption 1 and Lemma 5, p. 14

import Mathlib
import Definitions.Def_InfFisher_Linear_Setting

namespace InfFisher.Linear

open MeasureTheory

/-- Gao–Kroer, Lemma 5: the equilibrium partition under Assumption 1. -/
theorem lemma_5 {n : ℕ} (hn : 0 < n) (c d : ℕ → ℝ)
    (hA : Assumption1 n c d) (B : Fin n → ℝ) (hB : ∀ i, 0 < B i) :
    ∃ a : ℕ → ℝ,
      a 0 = 0 ∧ a n = 1 ∧
      (∀ k < n, a k < a (k + 1)) ∧
      (∃ p, IsME (volume.restrict (Set.Icc (0 : ℝ) 1))
        (linVal c d n) B
        (fun i => (Set.Icc (a i.val) (a (i.val + 1))).indicator (fun _ => (1 : ℝ))) p) ∧
      ∀ x p, IsME (volume.restrict (Set.Icc (0 : ℝ) 1)) (linVal c d n) B x p →
        let μ := volume.restrict (Set.Icc (0 : ℝ) 1)
        let v := linVal c d n
        let β : Fin n → ℝ := fun i => B i / pair μ (v i) (x i)
        (∀ i, x i =ᵐ[μ]
          (Set.Icc (a i.val) (a (i.val + 1))).indicator (fun _ => (1 : ℝ))) ∧
        p =ᵐ[μ] maxScaled v β ∧
        ∀ i : Fin n, ∀ θ ∈ Set.Ioo (a i.val) (a (i.val + 1)),
          ∀ j : Fin n, j ≠ i → β j * v j θ < β i * v i θ := by sorry

end InfFisher.Linear
