-- Prove2me | Theorems.Thm_NConjecture_abc_false_implies_n_false
-- name    : NConjecture.abc_false_implies_n_false
-- status  : Proved
-- author  : @LG
-- created : 2026-11-22T00:45:10.359457+00:00
-- url     : https://prove2.me/theorems/7e35edd6-ff71-4a56-b74e-53530d0f5d1c
-- title:
--   Failure of abc propagates to every $n \ge 4$
-- statement:
--   Hölzl–Kleine–Stephan, Theorem 3 (arXiv:2409.13439v2, p. 2), attributed there to Browkin–Brzeziński: "If the abc-conjecture is false then the $n$-conjecture is false for every $n\ge 4$." Equivalently (contrapositive), the $n$-conjecture at any single $n\ge 4$ implies abc. In $\varepsilon$-form: if abc fails — some $\varepsilon>0$ admits arbitrarily large coprime triples with $c\ge K\operatorname{rad}(abc)^{1+\varepsilon}$ for every $K$ — then `conjAt n` fails for every $n\ge 4$.
--
--   The mechanism (HKS Remark 5(2), Browkin–Brzeziński Remark 2) is the quadruple $(a^3,b^3,c^3,-3abc)$ built from an abc triple: it is admissible and has quality $\approx 3\,L(a,b,c)$, so quality $>1$ for abc triples forces quality $>3=2\cdot4-5$ for quadruples; higher $n$ use the analogous identities.
--
--   **Formalization Note.** The hypothesis is the negation of the full platform abc statement `abc_conjecture_strong`; the conclusion is `¬ conjAt n`. The statement is the $\varepsilon$-rendering of HKS Theorem 3 (the source phrases it via $Q_{A(n)}=2n-5$, equivalent to `conjAt n` given the proved lower bound).
-- source:
--   R. Hölzl, S. Kleine, F. Stephan, Improved lower bounds for strong n-conjectures, arXiv:2409.13439v2 (2025). https://arxiv.org/abs/2409.13439 Theorem 3 p. 2 (attributed to Browkin–Brzeziński); construction in Remark 5(2)–(4) p. 3. Cf. J. Browkin, J. Brzeziński, Some remarks on the abc-conjecture, Math. Comp. 62(206) (1994), 931–939. https://cr.yp.to/bib/1994/browkin.pdf Remark 2 p. 934.

import Mathlib
import Definitions.Def_NConjecture_Defs

namespace NConjecture

theorem abc_false_implies_n_false (n : ℕ) (hn : 4 ≤ n)
    (h : ¬ ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧
      ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c →
        Nat.Coprime a b → Nat.Coprime b c → Nat.Coprime a c →
        a + b = c →
        (c : ℝ) < K * (∏ p ∈ (a * b * c).primeFactors, (p : ℝ)) ^ (1 + ε)) :
    ¬ conjAt n := by sorry

end NConjecture
