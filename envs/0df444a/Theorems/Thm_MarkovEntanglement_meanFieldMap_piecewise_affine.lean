-- Prove2me | Theorems.Thm_MarkovEntanglement_meanFieldMap_piecewise_affine
-- name    : MarkovEntanglement.meanFieldMap_piecewise_affine
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-08-28T02:22:41.5751+00:00
-- url     : https://prove2.me/theorems/5c623aa3-0f99-4aa7-961c-d562357bce7e
-- title:
--   The mean-field map is piecewise affine (Lem. 7)
-- statement:
--   Let $\nu$ be an injective priority index on the finite local state space $S$ — the paper's assumption $\nu_1 > \nu_2 > \cdots > \nu_{|S|}$, which is no loss of generality since state labels may be permuted — and let $\alpha$ be the activation fraction.
--
--   Then the mean-field map $\varphi$ of the induced index policy is a continuous function of the configuration, and it is affine on each of the $|S|$ priority regions: for every local state $x$ there are a matrix $K$ and a vector $b$ such that
--
--   $$\varphi(m) = K^{\top} m + b \qquad \text{for every configuration } m \text{ with } \sum_{\nu_y > \nu_x} m_y \le \alpha < \sum_{\nu_y > \nu_x} m_y + m_x.$$
--
--   The region condition says exactly that $x$ is the state in which the budget runs out. Inside it the behaviour of the policy is frozen: every state of strictly higher priority than $x$ is fully activated, every state of strictly lower priority is fully idle, and only $x$ itself is served fractionally, by the amount $\alpha - \sum_{\nu_y > \nu_x} m_y$ — which is linear in $m$. Injectivity of $\nu$ is what rules out ties, where two states would have to share the residual budget and the map would pick up a genuine minimum.
--
--   The affine pieces are what the stability analysis works with: the matrix attached to the region containing the fixed point $m^\ast$ is the linearisation of the dynamics there, and Lemma 11 asserts that it is a stable matrix.
-- source:
--   Shuze Chen and Tianyi Peng, 'Multi-agent Markov Entanglement', arXiv:2506.02385v3, Appendix I, p. 41, Lemma 7 (adapted from Lemma B.1 of Gast, Gaujal and Yan 2023)

import Mathlib
import Definitions.Def_markov_entanglement_meanfield

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglement

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Lemma 7 (Piecewise Affine).  The mean-field map of an index policy is continuous, and on
each of the `|S|` priority regions — the configurations at which a given state is the one the
budget runs out in — it is an affine function of the configuration.  The priority index is
assumed injective, which is the paper's `ν₁ > ν₂ > ⋯ > ν_{|S|}`. -/
theorem meanFieldMap_piecewise_affine
    (P0 P1 : Matrix S S ℝ) (ν : S → ℝ) (hν : Function.Injective ν) (α : ℝ) :
    Continuous (meanFieldMap P0 P1 ν α) ∧
      ∀ x : S, ∃ (K : Matrix S S ℝ) (b : S → ℝ),
        ∀ m : S → ℝ, (∀ z, 0 ≤ m z) → IsPriorityRegion ν α m x →
          meanFieldMap P0 P1 ν α m = fun z => (∑ y, m y * K y z) + b z := by
  sorry

/-! ### M3 — Lemma 8, entanglement is controlled by the configuration's deviation -/

end MarkovEntanglement
