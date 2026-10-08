-- Prove2me | Theorems.Thm_MultiChoiceSecretary_Alg_expected_abs_q_sub_le_sqrt
-- name    : MultiChoiceSecretary.Alg.expected_abs_q_sub_le_sqrt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:37:36.220202+00:00
-- url     : https://prove2.me/theorems/c7a3cb77-4772-4325-a455-e256079c63ef
-- title:
--   Proof sketch of Theorem 2.1, PDF p. 2 — q, the number of elements of Z exceeding y_ℓ, satisfies E|q − ℓ| ≤ √k
-- statement:
--   Let $S$ be a finite set of $n$ real numbers and $2 \le k \le n$, $\ell = \lfloor k/2\rfloor$. Let $Y$ be the set of the first $m$ arrivals of a uniformly random order of $S$, $m \sim B(n,1/2)$ independent, and $Z = S\setminus Y$. Let $y_\ell$ be the $\ell$-th largest element of $Y$ and $q$ the number of elements of $Z$ exceeding $y_\ell$. Then
--
--   $$\mathbb E\,|q - \ell| \;\le\; \sqrt k.$$
--
--   This controls how far the number of elements the algorithm can take after the $m$-th arrival is from $\ell$; it is the concentration step of the proof sketch of Theorem 2.1.
--
--   **Formalization Note.** $\ell = \lfloor k/2\rfloor$ is the algorithm's own. When $|Y| < \ell$ the threshold is $y_\ell = -\infty$ and $q = |Z|$, the convention of the algorithm. The hypothesis $k \le n$ is added: without it, for $n = 1$ and $k = 100$, $\mathbb E|q - \ell| = 49.5 > 10$.
-- source:
--   Kleinberg, A multiple-choice secretary algorithm with applications to online auctions, SODA 2005, PDF p. 2, proof sketch of Theorem 2.1, "Thus their sum q = Σ_{i=1}^{ℓ} q_i satisfies E(|q − ℓ|) ≤ √k."

import Mathlib
import Definitions.Def_MultiChoiceSecretary_Alg_Setting

namespace MultiChoiceSecretary.Alg

theorem expected_abs_q_sub_le_sqrt (S : Finset ℝ) (k : ℕ) (h2k : 2 ≤ k) (hkn : k ≤ S.card) :
    splitAvg S (fun Y => |((qCount S Y (k / 2) : ℕ) : ℝ) - ((k / 2 : ℕ) : ℝ)|) ≤
      Real.sqrt k := by sorry

end MultiChoiceSecretary.Alg
