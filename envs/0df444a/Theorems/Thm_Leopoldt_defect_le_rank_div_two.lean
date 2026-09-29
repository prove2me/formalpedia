-- Prove2me | Theorems.Thm_Leopoldt_defect_le_rank_div_two
-- name    : Leopoldt.defect_le_rank_div_two
-- status  : Open
-- author  : @kbuzzard
-- created : 2026-09-09T09:33:13.896745+00:00
-- url     : https://prove2.me/theorems/0c0119bc-b349-43b8-a7e5-1d09e06a54ec
-- title:
--   Waldschmidt's bound $\mathcal{D}_L(\mathbb{K}) \le r/2$
-- statement:
--   This is the strongest general bound on the Leopoldt defect obtained by transcendence methods, recorded in the historical notes of the source.
--
--   Let $p$ be a prime, let $\mathbb{K}$ be a number field, and let $r = \mathbb{Z}\text{-rk}(E) = r_1 + r_2 - 1$ be the $\mathbb{Z}$-rank of its unit group. Then
--   $$\mathcal{D}_L(\mathbb{K}) \;\le\; \frac{r}{2}.$$
--
--   In words: at least half of the expected $p$-adic rank of the units is always attained, so the $\mathbb{Z}_p$-rank of the $p$-adic closure $\bar{E}$ is at least $r/2$. No hypothesis is placed on $p$ beyond primality, and $\mathbb{K}$ is arbitrary.
--
--   The bound is due to Waldschmidt (1981). It is unconditional and applies to every number field, which makes it the natural yardstick for the conjecture: Leopoldt asserts $\mathcal{D}_L(\mathbb{K}) = 0$, and $r/2$ is how far the transcendence route has been pushed towards that in general. In particular it already settles the conjecture whenever $r \le 1$.
--
--   **Formalization Note** The right-hand side is truncated integer division of the unit rank by $2$. Because the defect is a natural number, this is equivalent to the real inequality $\mathcal{D}_L(\mathbb{K}) \le r/2$: a natural number bounded by $r/2$ is bounded by $\lfloor r/2 \rfloor$.
-- source:
--   Attribution and statement as given in Preda Mihailescu, On CM Z_p-extensions and the Leopoldt conjecture for CM fields, https://arxiv.org/abs/1105.4544, Section 1.2 (Historical notes), p. 4: 'Currently the strongest result based on Diophantine approximation was achieved by Waldschmidt, who proved that if r is the Z-rank of the units in the field K, then the Leopoldt defect satisfies D_L(K) <= r/2.' Original: M. Waldschmidt, Transcendance et exponentielles en plusieurs variables, Invent. Math. 63 (1981), https://doi.org/10.1007/BF01389194.

import Definitions.Def_LeopoldtDefect

open NumberField

namespace Leopoldt
theorem defect_le_rank_div_two (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] :
    defect p K ≤ Units.rank K / 2 := by sorry
end Leopoldt
