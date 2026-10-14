-- Prove2me | Theorems.Thm_IntMul_Kappa_jain_round7_framework
-- name    : IntMul.Kappa.jain_round7_framework
-- status  : Open
-- author  : @xuanji
-- created : 2026-10-11T19:57:07.703185+00:00
-- url     : https://prove2.me/theorems/8a216417-6d30-4a56-aa81-dfc655239a31
-- title:
--   Jain's round-seven construction from its network savings
-- statement:
--   **Jain's round seven, with its finite certificates factored out.** Let $h^{\mathrm{bit}}$ be the child-width histogram of the round-seven bit network (witness 1: PR #62 producer, lifted frames, late copies, deferred readouts, V leaves, staircase entrance corner), of width $529$ with $W_b=108516254$ roles, and $h^{\mathrm{cx}}$ that of the round-six complex network, of width $576$ with $W_c=207387136$ roles and rank sum $s_c=\sum_w w\,n^{\mathrm{cx}}_w$. Put $\beta=1/1000$. Let $a_b,a_c,\varepsilon,x,C_1,\kappa$ be real numbers with $a_b,a_c\ge0$ such that
--
--   1. $\displaystyle\sum_w n^{\mathrm{bit}}_w\Big(\frac{w}{529}\Big)^{1-a_b}<W_b$;
--   2. $\displaystyle\sum_w n^{\mathrm{cx}}_w\Big(\frac{w}{576}\Big)^{1-a_c}<W_c$;
--   3. the crude-guard assembly $\mathrm{CrudeAssembly}(a_b,a_c,\beta,\varepsilon,x,C_1,\kappa,576,s_c)$ holds.
--
--   Then integer multiplication is possible in time
--   $$T(n)=O\big(n(\lg n)^{1-\kappa}\big),\qquad \lg n=\max(\lceil\log_2 n\rceil,1),$$
--   by one deterministic multitape Turing machine with fixed alphabet and tape count.
--
--   This is the machine-level content of the round: the OpenAI construction, Colkitt's framework and Jain's two networks turn certified network savings into a multiplication algorithm. The finite certificates and the real-analysis steps (rigorous bounds for $\log$ and $\exp$ applied to the frozen histograms) are separate. The source states the result as conditional on the OpenAI manuscript and on Colkitt's framework, and assumes that stage two is the complement time-reversal of stage one.
--
--   **Formalization Note** $\mathrm{KappaBound}(\kappa)$ is from `IntMul_MultitapeModel`: one deterministic multitape Turing machine with fixed alphabet and tape count, correct for every $n\ge1$, with running time at most $c\,n\,(\lg n)^{1-\kappa}$ for $n\ge n_0$. The moment $\mathrm{histMoment}$, rank sum and $\mathrm{CrudeAssembly}$ are from `IntMul_KappaFramework`; the histograms are from `IntMul_KappaJainData`. All hypotheses are real-number statements; the source checks rational majorants of them.
-- source:
--   S. Jain, integer-mult-kappa, https://github.com/Swapnil-jain/integer-mult-kappa/tree/c05adfe1dfe85326dd6dcf12bfd53f435bd49bf3 — README 'Round seven', lean/Round7.lean (bitHist, cxHist, bit_moment, cx_moment, kappa_assembly), research/round7-moment-refinement (sharper moment certificate, merged PR #2, commit 44e13e3), scripts/certificate_round3.py (crude guard, beta=1/1000); conditional on OpenAI, Integer multiplication below n log n, preprint, 23 September 2026, https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026 and on D. Colkitt, https://github.com/CrocSwap/integer-mult-bounds/tree/56b66d58297deca1d7dd130247d720e960f77a37

import Definitions.Def_IntMul_MultitapeModel
import Definitions.Def_IntMul_KappaFramework
import Definitions.Def_IntMul_KappaJainData

namespace IntMul.Kappa

theorem jain_round7_framework (ab ac ε x C₁ κ : ℝ) (hab : 0 ≤ ab) (hac : 0 ≤ ac)
    (hbit : histMoment Jain.bitR7 529 (1 - ab) < 108516254)
    (hcx : histMoment Jain.cxR6 576 (1 - ac) < 207387136)
    (hasm : CrudeAssembly ab ac (1 / 1000) ε x C₁ κ 576 (histRankSum Jain.cxR6)) :
    KappaBound κ := by sorry

end IntMul.Kappa
