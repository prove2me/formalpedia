-- Prove2me | Theorems.Thm_OAI_EuclideanSteinitzBergstrom_signing_implies_ordering
-- name    : OAI.EuclideanSteinitzBergstrom.signing_implies_ordering
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T19:19:25.256997+00:00
-- url     : https://prove2.me/theorems/d5fe5d7a-5bcf-415c-9f62-6407037dfd76
-- title:
--   Chobanyan's transference: a prefix bound C√d for signings implies the same prefix bound C√d for orderings of zero-sum families
-- statement:
--   For $d \ge 1$ let $\mathbb R^d$ carry the Euclidean norm (`Vector d`, which is `EuclideanSpace ℝ (Fin d)`). For a real number $C$, the two properties below come from the published bundle `Def_SteinitzBergstrom`.
--
--   `SignedPrefixBound C`: for all natural numbers $d, N \ge 1$ and all vectors $v_0, \dots, v_{N-1} \in \mathbb R^d$ with $\|v_i\| \le 1$, there are signs $\varepsilon_i \in \{-1, 1\}$ such that for every $k \le N$
--   $$\Bigl\|\sum_{i < k} \varepsilon_i v_i\Bigr\| \le C\sqrt d.$$
--
--   `OrderingPrefixBound C`: for all natural numbers $d, N \ge 1$ and all vectors $v_0, \dots, v_{N-1} \in \mathbb R^d$ with $\|v_i\| \le 1$ and $\sum_i v_i = 0$, there is a permutation $\pi$ of $\{0, \dots, N-1\}$ (`Equiv.Perm (Fin N)`) such that for every $k \le N$
--   $$\Bigl\|\sum_{i < k} v_{\pi(i)}\Bigr\| \le C\sqrt d.$$
--
--   **Statement.** For every real number $C$, `SignedPrefixBound C` implies `OrderingPrefixBound C`, with the same constant $C$.
--
--   This is Chobanyan's transference principle between signed sums and rearrangements (S. Chobanyan, 1994), in its finite positive-forward, negative-reverse form: from an optimal ordering and a good signing of it, listing the positively signed vectors in order and then the negatively signed ones in reverse order gives prefixes of norm at most the average of the two bounds.
--
--   Lean: `OAI.EuclideanSteinitzBergstrom.signing_implies_ordering`, OpenAI's theorem of that name (in `lean/OAI/Analysis/Steinitz/Transference.lean`). Its only definitions, `Vector`, `SignedPrefixBound` and `OrderingPrefixBound`, are those of the published bundle `Def_SteinitzBergstrom`, the bundle of the target statement `OAI.EuclideanSteinitzBergstrom.main`.
-- source:
--   S. Chobanyan, Convergence a.s. of rearranged random series in Banach space and associated inequalities, in Probability in Banach Spaces 9, Progr. Probab. 35, Birkhäuser, 1994, 3–29 (the transference principle), in the finite positive-forward, negative-reverse form of S. Chobanyan, L. Chobanyan, Z. Gorgadze and G. Ghlonti, Bull. TICMI 27(1) (2023), 21–27, Theorem 2.1 and Remark 1; proof and Lean code: OpenAI, The Euclidean Steinitz–Bergström theorem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 097; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Steinitz/Transference.lean (declaration OAI.EuclideanSteinitzBergstrom.signing_implies_ordering)

import Mathlib
import Definitions.Def_SteinitzBergstrom

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace EuclideanSteinitzBergstrom

theorem signing_implies_ordering (C : ℝ) (h : SignedPrefixBound C) :
    OrderingPrefixBound C := by
  sorry

end EuclideanSteinitzBergstrom

end

end OAI
end
