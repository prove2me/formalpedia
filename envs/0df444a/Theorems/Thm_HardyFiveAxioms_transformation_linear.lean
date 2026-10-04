-- Prove2me | Theorems.Thm_HardyFiveAxioms_transformation_linear
-- name    : HardyFiveAxioms.transformation_linear
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T14:46:07.81887+00:00
-- url     : https://prove2.me/theorems/5e82a6ce-ffc4-4042-ad4d-3b56515f69cc
-- title:
--   State transformations are linear: $p\mapsto Zp$
-- statement:
--   Let $S\subseteq\mathbb R^K$ be a convex set of states containing the null state $0$. Let $g:\mathbb R^K\to\mathbb R^K$ describe the effect of a transformation device, with $g(0)=0$, such that $g$ respects mixtures on $S$:
--
--   $$g\big(\lambda p_A+(1-\lambda)p_B\big)=\lambda g(p_A)+(1-\lambda)g(p_B)\qquad(p_A,p_B\in S,\ 0\le\lambda\le1).$$
--
--   Then there is a real $K\times K$ matrix $Z$ with
--
--   $$g(p)=Zp\qquad\text{for all }p\in S .$$
--
--   This is Eq. (46) of the paper.
--
--   **Formalization Note** The hypothesis $g(0)=0$ expresses that an absent system stays absent. As for measurements, only a representation on $S$ is required.
-- source:
--   L. Hardy, *Quantum Theory From Five Reasonable Axioms*, arXiv:quant-ph/0101012v4 (2001), https://arxiv.org/abs/quant-ph/0101012, pp. 11–12, Section 6.7, Eq. (46)

import Mathlib

namespace HardyFiveAxioms

open Matrix

/-- Hardy 2001, Section 6.7, Eq. (46): a state transformation `p ↦ g(p)` that respects
mixtures on the convex set `S` of states (and sends the null state to the null state) acts on
`S` as a real `K × K` matrix: `g(p) = Z p`. -/
theorem transformation_linear {K : ℕ} (S : Set (Fin K → ℝ)) (hS : Convex ℝ S)
    (h0 : (0 : Fin K → ℝ) ∈ S) (g : (Fin K → ℝ) → (Fin K → ℝ)) (hg0 : g 0 = 0)
    (hmix : ∀ pA ∈ S, ∀ pB ∈ S, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      g (t • pA + (1 - t) • pB) = t • g pA + (1 - t) • g pB) :
    ∃ Z : Matrix (Fin K) (Fin K) ℝ, ∀ p ∈ S, g p = Z *ᵥ p := by sorry

end HardyFiveAxioms
