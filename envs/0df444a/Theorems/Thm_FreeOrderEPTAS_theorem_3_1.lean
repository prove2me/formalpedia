-- Prove2me | Theorems.Thm_FreeOrderEPTAS_theorem_3_1
-- name    : FreeOrderEPTAS.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:28:31.71104+00:00
-- url     : https://prove2.me/theorems/e8d4bbe8-0253-43f4-a7e1-af171faacfe4
-- title:
--   Theorem 3.1 — EPTAS for Free-Order Prophets (corrected: the algorithm of §§2–3 as repaired)
-- statement:
--   There are $t$ and a universal $d$ such that, for every $\varepsilon>0$, every $n$, every instance of $n$ independent non-negative integrable random variables, every LP solver and every rounding with (P1)–(P3), the program `freeOrder`, which reaches the laws only through a counted oracle for $\mathbb E[\max\{X_i,v\}]$, satisfies:
--
--   1. with probability at least $1/2$, the returned permutation has
--   $$V(\sigma)\ge(1-\varepsilon)\cdot\mathrm{OPT};$$
--   2. on every outcome, the counted cost is at most $t(\lceil1/\varepsilon\rceil)(n+1)^d$, and every LP and rounding instance has size at most $t(\lceil1/\varepsilon\rceil)(n+1)$.
--
--   Without the bound on the cost the claim is trivial, by trying all $n!$ orders; the bound is the content, and the exponent of $n$ is independent of $\varepsilon$.
--
--   Differences from the source:
--   - correction: the algorithm of §§2–3 as printed: closed jump intervals and the text’s bucket indexing, the BaseGuess grid up to $(1-\epsilon^2)E$, and the small-load guess up to order $n$ values → the program uses half-open jump intervals with Figure 1’s buckets, the extended grid, and the capped guess; reason: the printed forms fail on instances meeting all assumptions: $\epsilon=1/2$, values $(1,0,0,0,0)$ gives $K\ge4$; $\epsilon=1/2$, values $(1,0.9)$, $E=0.5$ has no grid guess; $n$ jobs of load $\delta$ give order $n$ small-load guesses per triple; Theorem 3.1 is existential, and this repaired algorithm is its witness
--   - reading: "$t(\epsilon)\cdot\mathrm{poly}(n)$-time algorithm", with an oracle returning a real number and an LP solved inside → unit-cost real arithmetic, comparisons, floors, ceilings and logs; one counted call per oracle query, LP solve and rounding; instance sizes bounded by $t(\epsilon)(n+1)$; reason: the two primitives of the proof cannot both live in the bit model; with any polynomial LP solver and the polynomial GKPS procedure this gives $t(\epsilon)\cdot\mathrm{poly}(n)$
--   - reading: "finds a permutation" → finds one with probability at least $1/2$; reason: the only engine, Theorem 2.1, is randomized, and §3 adds no derandomization
--   - reading: "guess" the parameters, pp.10, 18 → enumerate every guess vector, verify, keep what passes; reason: a deterministic reading of guessing
--   - encoding: independent random variables; "non-negative", p.3; finite means implied by the oracle → a product measure of probability laws on $[0,\infty)$ with finite mean; reason: pp.3, 17; the oracle presupposes finite $\mathbb E[\max\{X_i,v\}]$
--   - encoding: $1/\epsilon$ an integer; the slack $(1-7\epsilon)$ → the program runs at $\epsilon=1/\lceil14/\min\{\varepsilon,1\}\rceil$; reason: "without loss of generality", p.17
--   - reading: $\mathrm{OPT}=V(\sigma^*)$ for an optimal policy → the maximum of $V$ over permutations; reason: p.17 defines it so; Hill’s theorem is not needed
--   - reading: $V(\sigma)$, "the expected value obtained by an algorithm that utilizes the optimal stopping rule on $\sigma$" → the supremum over measurable stopping rules of the expected reward; reason: the operational meaning of the phrase; `value_eq_recursion` links it to the recursion
--   - reading: §3.5 orders only the variables the assignment places → unassigned variables come after all assigned ones; reason: §3.5 is silent; a total permutation is needed
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, Theorem 3.1, p.17 (= Theorem 1.1, p.4)

import Mathlib
import Definitions.Def_FreeOrderEPTAS_OPT
import Definitions.Def_FreeOrderEPTAS_freeOrder
import Definitions.Def_FreeOrderEPTAS_orc

namespace FreeOrderEPTAS

/-- Theorem 3.1, p.17 (= Theorem 1.1, p.4) (arXiv:2007.13121v3), about the program `freeOrder`, which
reaches the laws only through the counted oracle `E[max{X_i, v}]`: for every `ε > 0`, with probability
at least 1/2 the returned permutation has `V(σ) ≥ (1 - ε) OPT`, and on every outcome the counted
cost is at most `t(⌈1/ε⌉) (n + 1)^d` and the LP and rounding instances have size at most
`t(⌈1/ε⌉) (n + 1)`, with `d` universal. -/
theorem theorem_3_1 :
    ∃ (t : ℕ → ℕ) (d : ℕ), ∀ (ε : ℝ), 0 < ε → ∀ (n : ℕ) (I : Instance n) (lp : LPSolver)
      (rnd : Rounding), IsLPSolver lp → IsDependentRounding rnd →
      (1 / 2 : ℝ) ≤ pr ((freeOrder ε (orc I) lp rnd).run 0) {r | (1 - ε) * OPT I ≤ V I r.1} ∧
      ∀ r ∈ ((freeOrder ε (orc I) lp rnd).run 0).support,
        r.2.total ≤ t ⌈1 / ε⌉₊ * (n + 1) ^ d ∧ r.2.maxSize ≤ t ⌈1 / ε⌉₊ * (n + 1) := by sorry

end FreeOrderEPTAS
