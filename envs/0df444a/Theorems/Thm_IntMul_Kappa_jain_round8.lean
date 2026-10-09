-- Prove2me | Theorems.Thm_IntMul_Kappa_jain_round8
-- name    : IntMul.Kappa.jain_round8
-- status  : Open
-- author  : @avi
-- created : 2026-10-09T04:47:45.819987+00:00
-- url     : https://prove2.me/theorems/bc50ead5-e2f6-4fdd-a388-37e0da278e52
-- title:
--   Exact integer multiplication with saving κ = 0.00012612978530233
-- statement:
--   **Jain's round-eight witness.** There is one deterministic multitape Turing machine, with a fixed finite alphabet and a fixed number of tapes, that for every $n\ge1$ and all $x,y\in\{0,1\}^n$ halts on input $x\#y$ with output $\operatorname{bin}_{2n}(\operatorname{val}x\cdot\operatorname{val}y)$, and whose worst-case running time satisfies
--   $$T(n)=O\big(n\,L(n)^{1-\kappa}\big),\qquad L(n)=\max(\lceil\log_2n\rceil,1),\qquad \kappa=\frac{12612978530233}{10^{17}}=0.00012612978530233>2^{-13}.$$
--
--   This is the strongest exponent saving claimed so far in the line of work started by the OpenAI preprint: S. Jain's round eight. The project states that the claim is conditional on the OpenAI manuscript and on Colkitt's framework, that stage two and three further interfaces are assumed rather than machine-checked, and that it has not had independent review. Its finite rational certificates are checked in the Lean kernel; the analytic inequalities they rely on and the machine construction are not. This is the full bound with no assumed algorithmic or analytic framework. Its proof is Open.
--
--   **Formalization Note** `KappaBound κ` is from the shared `IntMul_MultitapeModel`: one machine correct for every $n\ge1$, and constants $c>0$, $n_0$ with running time at most $c\,n\,L(n)^{1-\kappa}$ for $n\ge n_0$. The decimal literal is the exact rational $0.00012612978530233=12612978530233/10^{17}$.
-- source:
--   S. Jain, Integer multiplication: a conditional witness above 2^-13 (integer-mult-kappa), research draft, https://github.com/Swapnil-jain/integer-mult-kappa/tree/5868dc701a9bec375c9dc5391d992ab3b8c35f3f — README headline and 'Round eight' section (scripts/certificate_round8.py, certificates/round8/, lean/Round8.lean); kappa = 12612978530233/10^17, bound by the complex side; stated as conditional on OpenAI, Integer multiplication below n log n, preprint, 23 September 2026, https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, and on D. Colkitt, https://github.com/CrocSwap/integer-mult-bounds/tree/56b66d58297deca1d7dd130247d720e960f77a37

import Definitions.Def_IntMul_MultitapeModel

namespace IntMul.Kappa

theorem jain_round8 : KappaBound (0.00012612978530233 : ℝ) := by
  sorry

end IntMul.Kappa
