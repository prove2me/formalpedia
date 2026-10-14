-- Prove2me | Theorems.Thm_IntMul_Kappa_jain_round8_framework
-- name    : IntMul.Kappa.jain_round8_framework
-- status  : Open
-- author  : @xuanji
-- created : 2026-10-11T19:59:05.925842+00:00
-- url     : https://prove2.me/theorems/44d4faef-6e13-42ea-8f32-68deb36d915e
-- title:
--   Jain's round-eight construction from its network savings
-- statement:
--   **Jain's round eight, with its finite certificates factored out.** Let $h^{\mathrm{old}}$ be the child-width histogram of the round-seven bit network (witness 2, round-six entrance corner), $h^{\mathrm{bit}}$ that of the round-eight bit network (opposite bank orders on the same witness), and $h^{\mathrm{cx}}$ that of the round-eight complex network (signed reclaim and completed-core sharing), with rank sum $s_c=\sum_w w\,n^{\mathrm{cx}}_w$. Put $\theta=\beta=1/1000$. Let $a_{\mathrm{old}},a^*,a_b,a_c,\varepsilon,x,C_1,\kappa$ be real numbers with $a_{\mathrm{old}},a^*,a_c\ge0$ such that
--
--   1. $\displaystyle\sum_w n^{\mathrm{old}}_w\Big(\frac{w}{529}\Big)^{1-a_{\mathrm{old}}}<104719230$;
--   2. $\displaystyle\sum_w n^{\mathrm{bit}}_w\Big(\frac{w}{529}\Big)^{1-a^*}<104719230$;
--   3. $a_b=(1-\theta)a^*+\theta a_{\mathrm{old}}$ and $a_b<\theta$ (the stopped bit interchange);
--   4. $\displaystyle\sum_w n^{\mathrm{cx}}_w\Big(\frac{w}{576}\Big)^{1-a_c}<12869228$;
--   5. the crude-guard assembly $\mathrm{CrudeAssembly}(a_b,a_c,\beta,\varepsilon,x,C_1,\kappa,576,s_c)$ holds.
--
--   Then integer multiplication is possible in time
--   $$T(n)=O\big(n(\lg n)^{1-\kappa}\big),\qquad \lg n=\max(\lceil\log_2 n\rceil,1),$$
--   by one deterministic multitape Turing machine with fixed alphabet and tape count.
--
--   This is the machine-level content of Jain's round eight: the OpenAI construction, Colkitt's framework and Jain's networks turn certified network savings into a multiplication algorithm. The finite certificates and the real-analysis steps (rigorous bounds for $\log$ and $\exp$ applied to the frozen histograms) are separate. The source states the result as conditional on the OpenAI manuscript and on Colkitt's framework, and lists as assumed interfaces: stage two is the complement time-reversal of stage one; the normal form for alternating residuals (icekylinx, PRs #24 and #104); binary address adapters for the exterior children of the sharing; and the row stock of the stopped bit interchange.
--
--   **Formalization Note** $\mathrm{KappaBound}(\kappa)$ is from `IntMul_MultitapeModel`: one deterministic multitape Turing machine with fixed alphabet and tape count, correct for every $n\ge1$, with running time at most $c\,n\,(\lg n)^{1-\kappa}$ for $n\ge n_0$. The moment $\mathrm{histMoment}$, rank sum and $\mathrm{CrudeAssembly}$ are from `IntMul_KappaFramework`; the histograms are from `IntMul_KappaJainData`. All hypotheses are real-number statements; the source checks rational majorants of them.
-- source:
--   S. Jain, integer-mult-kappa, https://github.com/Swapnil-jain/integer-mult-kappa/tree/5868dc701a9bec375c9dc5391d992ab3b8c35f3f — README 'Round eight' (savings, stopped mix a_b=(1-theta)a*+theta a_old with theta=1/1000, a_old = round-seven saving of witness 2, proof interfaces), scripts/certificate_round8.py, scripts/certificate_round3.py (crude guard, beta=1/1000), lean/Round8.lean (bit_moment, bit_stopped, cx_moment, kappa_assembly), lean/Round7.lean (bitplain_moment); conditional on OpenAI, Integer multiplication below n log n, preprint, 23 September 2026, https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026 and on D. Colkitt, https://github.com/CrocSwap/integer-mult-bounds/tree/56b66d58297deca1d7dd130247d720e960f77a37

import Definitions.Def_IntMul_MultitapeModel
import Definitions.Def_IntMul_KappaFramework
import Definitions.Def_IntMul_KappaJainData

namespace IntMul.Kappa

theorem jain_round8_framework (aOld aStar ab ac ε x C₁ κ : ℝ)
    (hOld : 0 ≤ aOld) (hStar : 0 ≤ aStar) (hac : 0 ≤ ac)
    (hbitOld : histMoment Jain.bitR7plain 529 (1 - aOld) < 104719230)
    (hbit : histMoment Jain.bitR8 529 (1 - aStar) < 104719230)
    (hstop : ab = (1 - 1 / 1000) * aStar + 1 / 1000 * aOld)
    (hθ : ab < 1 / 1000)
    (hcx : histMoment Jain.cxR8 576 (1 - ac) < 12869228)
    (hasm : CrudeAssembly ab ac (1 / 1000) ε x C₁ κ 576 (histRankSum Jain.cxR8)) :
    KappaBound κ := by sorry

end IntMul.Kappa
