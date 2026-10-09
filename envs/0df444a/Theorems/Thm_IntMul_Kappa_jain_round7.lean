-- Prove2me | Theorems.Thm_IntMul_Kappa_jain_round7
-- name    : IntMul.Kappa.jain_round7
-- status  : Open
-- author  : @avi
-- created : 2026-10-09T02:16:38.180368+00:00
-- url     : https://prove2.me/theorems/2a6f671f-d2e8-4d0c-ac71-175f8e055072
-- title:
--   Exact integer multiplication with saving κ = 0.00006397891967576
-- statement:
--   **Jain's round-seven witness.** There is one deterministic multitape Turing machine, with a fixed finite alphabet and a fixed number of tapes, that for every $n\ge1$ and all $x,y\in\{0,1\}^n$ halts on input $x\#y$ with output $\operatorname{bin}_{2n}(\operatorname{val}x\cdot\operatorname{val}y)$, and whose worst-case running time satisfies
--   $$T(n)=O\big(n\,L(n)^{1-\kappa}\big),\qquad L(n)=\max(\lceil\log_2n\rceil,1),\qquad \kappa=\frac{799736495947}{12500000000000000}=0.00006397891967576>2^{-14}.$$
--
--   This is the strongest exponent saving claimed so far in the line of work started by the OpenAI preprint: S. Jain's round seven with the sharper moment certificate merged into the same repository. The project states that the claim is conditional on the OpenAI manuscript and on Colkitt's framework, that stage two is assumed rather than machine-checked, and that it has not had independent review. Its finite rational certificates are checked in the Lean kernel; the analytic inequalities they rely on and the machine construction are not. This is the full bound with no assumed algorithmic or analytic framework. Its proof is Open.
--
--   **Formalization Note** `KappaBound κ` is from the shared `IntMul_MultitapeModel`: one machine correct for every $n\ge1$, and constants $c>0$, $n_0$ with running time at most $c\,n\,L(n)^{1-\kappa}$ for $n\ge n_0$. The decimal literal is the exact rational $0.00006397891967576=799736495947/12500000000000000$.
-- source:
--   S. Jain, Integer multiplication: a conditional witness above 2^-14 (integer-mult-kappa), research draft, https://github.com/Swapnil-jain/integer-mult-kappa/tree/c05adfe1dfe85326dd6dcf12bfd53f435bd49bf3 — README 'Round seven' (lean/Round7.lean, scripts/certificate_round7.py, notes/deferred-readout.tex) and research/round7-moment-refinement/README.md (sharper moment certificate, merged PR #2, commit 44e13e3; conditional kappa = 799736495947/12500000000000000 = 0.00006397891967576); stated as conditional on OpenAI, Integer multiplication below n log n, preprint, 23 September 2026, https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, and on D. Colkitt, https://github.com/CrocSwap/integer-mult-bounds/tree/56b66d58297deca1d7dd130247d720e960f77a37

import Definitions.Def_IntMul_MultitapeModel

namespace IntMul.Kappa

theorem jain_round7 : KappaBound (0.00006397891967576 : ℝ) := by
  sorry

end IntMul.Kappa
