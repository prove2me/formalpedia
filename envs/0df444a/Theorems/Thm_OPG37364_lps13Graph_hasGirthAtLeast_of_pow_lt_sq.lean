-- Prove2me | Theorems.Thm_OPG37364_lps13Graph_hasGirthAtLeast_of_pow_lt_sq
-- name    : OPG37364.lps13Graph_hasGirthAtLeast_of_pow_lt_sq
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-11T00:23:13.709579+00:00
-- url     : https://prove2.me/theorems/3535df2e-0a4c-40f5-8163-709cd207b218
-- title:
--   An explicit girth threshold for the fixed-13 LPS Cayley graph
-- statement:
--   Let q>13 be prime, choose any i∈𝔽_q with i²=−1, and let g be a nonnegative integer. Let X be the existing fixed-p=13 LPS Cayley graph on PGL₂(𝔽_q), defined by the original fourteen norm-13 integral quaternion generators and right multiplication. Then
--
--   $$13^g<q^2\quad\Longrightarrow\quad\text{every simple cycle in }X\text{ has length at least }g.$$
--
--   This gives an explicit, deliberately coarse sufficient size threshold for any prescribed girth, uniformly in the chosen square root i. Connectedness and quadratic nonresiduosity of 13 are not required.
--
--   Formalization note: X is exactly OPG37364.lps13Graph hq i and the conclusion is the original OPG37364.HasGirthAtLeast cycle-list predicate, including its convention for graphs without cycles.
-- source:
--   Classical norm/divisibility girth mechanism: Davidoff–Sarnak–Valette, Elementary Number Theory, Group Theory, and Ramanujan Graphs, Lemma 4.3.2 and Proposition 4.3.3, printed pp.117–118, https://math.bme.hu/~gabor/oktatas/SztoM/DavidoffSarnakValette.pdf ; Xavier Dahan, Regular graphs of large girth and arbitrary degree, arXiv:1110.5259, section 2.3, https://arxiv.org/pdf/1110.5259 . This fixed-13 formalization uses the already-Proved reduced-word primitivity theorem instead of general quaternion normal forms, and proves a deliberately coarse integer threshold directly for the original full PGL Cayley graph. The sources are not claimed to contain this exact Lean packaging or threshold statement; no mathematical novelty is claimed.

import Definitions.Def_opg37364_lps13
set_option autoImplicit false

namespace OPG37364

theorem lps13Graph_hasGirthAtLeast_of_pow_lt_sq
    {q : ℕ} [Fact q.Prime] (hq : 13 < q) (i : LPS13Root q)
    (g : ℕ) (hbound : 13^g < q^2) : HasGirthAtLeast (lps13Graph hq i) g := by sorry

end OPG37364
