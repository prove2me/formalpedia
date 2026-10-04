-- Prove2me | Theorems.Thm_HardyFiveAxioms_measured_probability_linear
-- name    : HardyFiveAxioms.measured_probability_linear
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T14:24:53.873478+00:00
-- url     : https://prove2.me/theorems/d783626f-cb46-4dc7-adae-50d70076d281
-- title:
--   Measured probabilities are linear in the state: $p_{\rm meas}=r\cdot p$
-- statement:
--   Let $S\subseteq\mathbb R^K$ be a convex set of states containing the null state $0$. Let $f:\mathbb R^K\to\mathbb R$ be a measured probability with $f(0)=0$ that respects mixtures on $S$:
--
--   $$f\big(\lambda p_A+(1-\lambda)p_B\big)=\lambda f(p_A)+(1-\lambda)f(p_B)\qquad(p_A,p_B\in S,\ 0\le\lambda\le1).$$
--
--   Then there is a vector $r\in\mathbb R^K$ such that
--
--   $$f(p)=r\cdot p=\sum_{k=1}^K r_kp^k\qquad\text{for all }p\in S .$$
--
--   This is Eq. (44) of the paper, proved in Appendix 1: every probability measurement is represented by a measurement vector $r$.
--
--   **Formalization Note** The paper's Appendix 1 extends Eq. (112) beyond $S$ by fiat ("we are free to impose"). The present statement only asks for a linear representation on $S$ itself, which needs no such extension. The hypothesis $f(0)=0$ expresses that the null state never produces a non-null outcome.
-- source:
--   L. Hardy, *Quantum Theory From Five Reasonable Axioms*, arXiv:quant-ph/0101012v4 (2001), https://arxiv.org/abs/quant-ph/0101012, p. 11, Section 6.6, Eqs. (41)–(44); pp. 28–29, Appendix 1, Eqs. (107)–(117)

import Mathlib

namespace HardyFiveAxioms

/-- Hardy 2001, Section 6.6, Eq. (44) and Appendix 1: a measured probability `f(p)` that
respects mixtures on the convex set `S` of states (which contains the null state, on which
`f` vanishes) is given by a linear functional `p_meas = r · p`. -/
theorem measured_probability_linear {K : ℕ} (S : Set (Fin K → ℝ)) (hS : Convex ℝ S)
    (h0 : (0 : Fin K → ℝ) ∈ S) (f : (Fin K → ℝ) → ℝ) (hf0 : f 0 = 0)
    (hmix : ∀ pA ∈ S, ∀ pB ∈ S, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      f (t • pA + (1 - t) • pB) = t * f pA + (1 - t) * f pB) :
    ∃ r : Fin K → ℝ, ∀ p ∈ S, f p = ∑ k, r k * p k := by sorry

end HardyFiveAxioms
