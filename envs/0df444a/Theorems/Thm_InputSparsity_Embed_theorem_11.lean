-- Prove2me | Theorems.Thm_InputSparsity_Embed_theorem_11
-- name    : InputSparsity.Embed.theorem_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T10:18:14.322189+00:00
-- url     : https://prove2.me/theorems/ac1dfc6f-5297-4ddc-a448-efe3f376cd7f
-- title:
--   Theorem 11, p. 11 — sparse subspace embedding with probability at least 9/10
-- statement:
--   There is an absolute constant $C>0$ such that the following holds for every real matrix $A\in\mathbb R^{n\times d}$ of rank $r\ge1$, every $0<\varepsilon\le1/2$, and every integer $t$ satisfying $t\ge C(r/\varepsilon)^4\log^2(r/\varepsilon)$. Draw one sparse sketch $S=\Phi D$ using an independent uniform bucket for each input coordinate and an independent fair sign. Then
--
--   $$\Pr\!\left(\forall y\in C(A),\quad\left|\|Sy\|_2^2-\|y\|_2^2\right|\le\varepsilon\|y\|_2^2\right)\ge\frac9{10}.$$
--
--   The same sketch therefore preserves every vector in the column space at once. This is the paper's core sparse subspace-embedding guarantee.
--
--   **Formalization Note** The squared-norm form is what the proof delivers and implies the printed norm form. The paper's $n>d$ and nonzero-entry assumptions concern running time. The running-time sentence and a printed refined bound on $t$ with an inverted collision factor are not part of this mathematical statement. The range of $\varepsilon$ and $r\ge1$ exclude degenerate logarithms and vacuous lower bounds.
-- source:
--   Clarkson and Woodruff, Low Rank Approximation and Regression in Input Sparsity Time, arXiv:1207.6365v4, p. 11, Theorem 11

import Mathlib
import Definitions.Def_InputSparsity_Embed_SparseEmbedding

namespace InputSparsity.Embed
open Matrix

/-- Clarkson--Woodruff, Theorem 11, p. 11: one sparse random sketch embeds the whole column space. -/
theorem theorem_11 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n d r t : ℕ) (A : Matrix (Fin n) (Fin d) ℝ),
        A.rank = r → 1 ≤ r →
        ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
          C * ((r : ℝ) / ε) ^ 4 *
            (Real.log ((r : ℝ) / ε)) ^ 2 ≤ (t : ℝ) →
          (9 : ℝ) / 10 ≤ unifProb (Omega n t)
            {ω | ∀ x : Fin d → ℝ,
              |sqNorm (sketch ω.1 ω.2 *ᵥ (A *ᵥ x)) - sqNorm (A *ᵥ x)| ≤
                ε * sqNorm (A *ᵥ x)} := by sorry

end InputSparsity.Embed
