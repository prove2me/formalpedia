-- Prove2me | Theorems.Thm_MarkovMixing_evolving_sets_root_contraction
-- name    : MarkovMixing.evolving_sets_root_contraction
-- status  : Proved
-- author  : @steven
-- created : 2026-08-22T22:34:02.145387+00:00
-- url     : https://prove2.me/theorems/99a5019d-9a40-43bb-9c0b-b6552acd5c0f
-- title:
--   Lemma 17.16 — root-profile contraction for evolving sets
-- statement:
--   Let $P$ be a lazy finite Markov chain with strictly positive stationary distribution $\pi$, and let $S'$ be one step of the evolving-set process from $S$. Write $\pi(A)=\sum_{x\in A}\pi(x)$ and $A^\sharp$ for whichever of $A$ and $A^c$ has stationary mass at most one half. Then Lemma 17.16 asserts the conditional contraction $$\mathbb E_S\sqrt{\pi((S')^\sharp)}\le\left(1-\frac{\Phi_\star^2}{2}\right)\sqrt{\pi(S^\sharp)}.$$ The formal statement writes $\pi(A^\sharp)=\min(\pi(A),1-\pi(A))$ directly.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, Chapter 17, Lemma 17.16, Equation (17.26), p. 252, https://pages.uoregon.edu/dlevin/MARKOV/markovmixing.pdf

import Definitions.Def_mm_martingale
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace MarkovMixing

/-- **Lemma 17.16** (LPW): one evolving-set step contracts the square-root profile by the bottleneck factor. -/
theorem evolving_sets_root_contraction {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hP : IsStochastic P)
    (π : V → ℝ) (hπ : IsStationary P π) (hpos : ∀ x : V, 0 < π x)
    (hlazy : ∀ x : V, 2⁻¹ ≤ P x x) (S : Finset V) :
    (∑ T : Finset V, evolvingSets P π S T *
      Real.sqrt (min (∑ x ∈ T, π x) (1 - ∑ x ∈ T, π x))) ≤
      (1 - bottleneckStar P π ^ 2 / 2) *
        Real.sqrt (min (∑ x ∈ S, π x) (1 - ∑ x ∈ S, π x)) := by
  sorry

end MarkovMixing
