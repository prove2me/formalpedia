-- Prove2me | Theorems.Thm_NetworkSumSecure_Solvability_theorem_5
-- name    : NetworkSumSecure.Solvability.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T05:04:06.182202+00:00
-- url     : https://prove2.me/theorems/910a7c6b-0724-4d5a-a9fc-13cd2bc12e9f
-- title:
--   Theorem 5 — complete algebraic criteria for decoding and sum-security
-- statement:
--   Fix a finite network $N$, a finite field $F$, security level $r\ge0$, key counts $z_i\ge0$, and arbitrary causal local linear encoding data. Let $g_e$ be its induced global columns, $G_\rho$ the incoming-server columns, and $\lambda$ the column with one in every user message coordinate and zero in key coordinates. Both equivalences hold:
--
--   $$\begin{aligned}
--   (\exists\text{ correct linear decoder})&\quad\Longleftrightarrow\quad\lambda\in\langle G_\rho\rangle,\\
--   \text{equation (7) holds}&\quad\Longleftrightarrow\quad\forall W\in\mathcal W_r,\ \lambda\notin\langle G_W\rangle.
--   \end{aligned}$$
--
--   The security predicate uses the exact uniform probability of existential-input key events. This result supplies both algebraic tests used in the transformation theorem.
--
--   **Formalization Note** Appendix A (58) selects a decoder from a column-span representation. Span membership alone does not certify a previously chosen arbitrary decoder. For example, over $\mathbb F_2$, one user and two parallel edges carrying $(m+k,k)$ satisfy the span and security criteria at $r=1$, while the chosen zero decoder is incorrect. This explains the decoder reading; it does not claim that the source's literal theorem under feasibility is false.
--
--   Differences from the source:
--   - generalization: a feasible scheme is fixed in Section 4's mincut≥r+1 regime → arbitrary causal linear encoding data on any model network, with no feasibility or cut-bound assumption; reason: Appendix A proves both tests using linear algebra without assuming feasibility or the cut bound, and every source instance is included
--   - reading: correctness is equivalent to target-column membership while the decoder is not explicitly reselected in the theorem sentence → existence of a correct linear decoder is equivalent to membership; reason: Appendix A (58) explicitly chooses the decoder; the fixed zero-decoder example explains why decoder existence is the intended criterion
--   - generalization: the section assumes a sufficiently large finite field and a nonempty set of participants → the algebraic equivalences hold over every finite field and allow an empty user set; reason: Appendix A uses finite linear algebra only; when there are no users both security and target-column exclusion fail
--   - encoding: independent uniform key probabilities and block vector coordinates → exact rational event-cardinality probabilities and dependent user-block coordinates; reason: finite product counting gives the same probabilities and global columns are induced by local execution
-- source:
--   Yang Bai, Xuan Guang, Lizhi Wang, STOC 2027 submission #1291 (October 2026), p. 13 (PDF p. 15); Appendix A pp. 25–31 (PDF pp. 27–33), Theorem 5, equations (22), (23), (56)–(78)

import Mathlib
import Definitions.Def_NetworkSumSecure_Solvability_algebra

namespace NetworkSumSecure.Solvability

/-- Theorem 5, printed p.13 (PDF 15), with the generalized arbitrary-encoding
and existential-decoder readings specified by Appendix A (56)–(78). -/
theorem theorem_5 {V E U F : Type} [Fintype V] [Fintype E] [Fintype U]
    [Field F] [Fintype F] (N : Network V E U) (r : ℕ)
    (z : U → ℕ) (C : LocalCode N F z) :
    ((∃ φ : Decoder N F, Correct C φ) ↔
      target (F := F) z ∈ columnSpan (globalColumn C) (incoming N N.server)) ∧
    (SumSecure C r ↔ ∀ W : Finset E, W.card ≤ r →
      target (F := F) z ∉ columnSpan (globalColumn C) W) := by sorry

end NetworkSumSecure.Solvability
