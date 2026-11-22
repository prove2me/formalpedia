-- Prove2me | Theorems.Thm_NConjecture_bb94_theorem_1
-- name    : NConjecture.bb94_theorem_1
-- status  : Proved
-- author  : @LG
-- created : 2026-11-22T00:44:40.228414+00:00
-- url     : https://prove2.me/theorems/3edb9ad9-84df-4d61-85ac-9a8d67fe7c04
-- title:
--   Browkin–Brzeziński Theorem 1 ($\limsup L_n \ge 2n-5$)
-- statement:
--   Browkin–Brzeziński's Theorem 1 (p. 933): "For every $n\ge 3$, $\limsup\{L_n\}\ge 2n-5$." Thus the conjectured exponent $2n-5$ cannot be lowered. In $\varepsilon$-form, for every $n\ge 3$ and every $\varepsilon>0$ there are infinitely many admissible $n$-tuples whose quality exceeds $2n-5-\varepsilon$:
--   $$\#\{a\text{ admissible}: M(a)>m(a)^{\,2n-5-\varepsilon}\}=\infty.$$
--   The source proves this by taking $k=n-3$ in Lemma 1 and substituting $x=-a_1/a_2$ to obtain a vanishing sum of $n$ terms (equation (7)); choosing $a_1=2^i$, $a_2=-1$ makes only the first summand positive, so no proper subsum vanishes and the gcd is $1$, while $M_n=2^{i(2n-5)}$ and $L_n\to 2n-5$ as $i\to\infty$.
--
--   **Formalization Note.** `admissible`, $M$ (`Finset.sup` of $|a_i|$) and $m$ (`Brocard.radical` of $\prod_i|a_i|$) are as in `NConjecture_Defs`. The strict inequality $M>m^{2n-5-\varepsilon}$ is equivalent to $L>2n-5-\varepsilon$ since $m\ge 2$; "infinitely many" is `Set.Infinite`, which is exactly $\limsup L_n\ge 2n-5$.
-- source:
--   J. Browkin, J. Brzeziński, Some remarks on the abc-conjecture, Math. Comp. 62(206) (1994), 931–939. https://cr.yp.to/bib/1994/browkin.pdf Theorem 1 p. 933; proof via Lemma 1 and equation (7), p. 934. Restated in R. Hölzl, S. Kleine, F. Stephan, Improved lower bounds for strong n-conjectures, arXiv:2409.13439v2 (2025). https://arxiv.org/abs/2409.13439 §1 p. 2 and Remark 19.

import Mathlib
import Definitions.Def_NConjecture_Defs

namespace NConjecture

theorem bb94_theorem_1 (n : ℕ) (hn : 3 ≤ n) (ε : ℝ) (hε : 0 < ε) :
    Set.Infinite {a : Fin n → ℤ | admissible n a ∧
      (Brocard.radical (∏ i, (a i).natAbs) : ℝ) ^ (2 * (n : ℝ) - 5 - ε) <
        ((Finset.univ.sup (fun i => (a i).natAbs) : ℕ) : ℝ)} := by sorry

end NConjecture
