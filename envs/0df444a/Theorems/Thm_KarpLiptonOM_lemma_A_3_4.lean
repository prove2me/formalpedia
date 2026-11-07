-- Prove2me | Theorems.Thm_KarpLiptonOM_lemma_A_3_4
-- name    : KarpLiptonOM.lemma_A_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:48:23.921199+00:00
-- url     : https://prove2.me/theorems/08728bc5-5cbf-49b9-afd5-62dab491d223
-- title:
--   Lemma A.3.4 = Fact (F3) — pseudorandom generators from oblivious orders
-- statement:
--   Fact (F3), which Lemma A.3.4 derives from the order-based definition of $\mathrm L^{\mathrm P}_2$: there are a language $B \in \mathrm{OL}^{\mathrm P}_2$ and a deterministic polynomial-time oracle algorithm that, given $1^N$, outputs with oracle $B$ a list $g_1, \dots, g_m \in \{0,1\}^N$ with $m = \mathrm{poly}(N)$ such that every $N$-input circuit $C$ of size at most $N$ satisfies
--   $$
--   \Bigl| \Pr_{i}\bigl[C(g_i) = 1\bigr] - \Pr_{y \in \{0,1\}^N}\bigl[C(y) = 1\bigr] \Bigr| \le \frac1N .
--   $$
--
--   An oracle in $\mathrm{OL}^{\mathrm P}_2$ thus yields deterministic pseudorandom strings; this is what lets an $\mathrm{OL}^{\mathrm P}_2$ oracle replace Arthur's coins in Theorem A.3.5.
--
--   Differences from the source:
--   - encoding: deterministic polynomial-time oracle machines with loose access to a promise oracle → OracleTM (work and query tape, one step per query, time |w|^k + k with every oracle), correct with every language consistent with the oracle, repeated queries allowed; reason: the paper's own form of loose access for deterministic machines (p.21); a standard machine model, polynomially equivalent to the others; the paper's assumption that machines never repeat a query (p.21) changes no class when the oracle is a fixed language
--   - encoding: binary strings, lengths polynomial in n (polynomials nondecreasing and at least 1, p.20), polynomial-time predicates on tuples → List Bool, lengths p.eval n for p : Polynomial ℕ (p ≥ 1 imposed only in L₂^P, OL₂^P and OMIN), predicates on u₁#⋯#u_k decided by the published CookPvsNP Turing machines; reason: Lean convention; same classes (a length polynomial with p(0) = 0 gives no new language or promise problem)
--   - encoding: a list g₁, …, g_m ∈ {0,1}^N with m = poly(N), Pr_i uniform over i ≤ m → the output string of length m·N cut into m consecutive blocks of N bits, m ≥ 1; Pr_i is the fraction of blocks; m is polynomial because the machine runs in polynomial time; reason: the list as one output string; m ≥ 1 is needed for Pr_i to be defined
--   - encoding: every N (the bound 1/N) → every N ≥ 1; reason: 1/N is undefined at N = 0
--   - encoding: N-input circuit of size at most N → Circuit N with at most N gates (constants, NOT, binary AND/OR); reason: standard circuit model; the paper fixes none
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), Lemma A.3.4, p.26 (Fact (F3), p.23)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_KarpLiptonOM_OLP2
import Definitions.Def_KarpLiptonOM_OracleTM_IsPolyTime
import Definitions.Def_KarpLiptonOM_OracleTM_out
import Definitions.Def_KarpLiptonOM_Circuit_eval
import Definitions.Def_KarpLiptonOM_countStr
import Definitions.Def_KarpLiptonOM_tupleEnc

namespace KarpLiptonOM

/-- Lemma A.3.4 = Fact (F3) (pp.26, 23): a language `B ∈ OL₂^P` and a polynomial-time oracle algorithm that on `1^N` outputs with oracle `B` a list `g₁, …, g_m ∈ {0,1}^N` such that every `N`-input circuit `C` of size at most `N` satisfies `|Pr_i[C(g_i) = 1] − Pr_y[C(y) = 1]| ≤ 1/N`.

Source: Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b).

**Formalization Note** Strings, machines and classes are those of the `KarpLiptonOM` definitions: oracle access through every language consistent with the oracle, lengths `Polynomial ℕ`, polynomial-time predicates decided by the published `CookPvsNP` machines. The item's natural-language statement lists every difference from the page. -/
theorem lemma_A_3_4 : ∃ B ∈ OLP2, ∃ (M : OracleTM) (k : ℕ), M.IsPolyTime k ∧ ∀ N : ℕ, 1 ≤ N →
    ∃ m : ℕ, 1 ≤ m ∧ (M.out B k (tupleEnc [List.replicate N true])).length = m * N ∧
      ∀ C : Circuit N, C.gates.length ≤ N →
        |(((Finset.range m).filter (fun i => C.eval
            (((M.out B k (tupleEnc [List.replicate N true])).drop (i * N)).take N) = true)).card : ℚ)
            / m - (countStr N (fun y => C.eval y = true) : ℚ) / 2 ^ N| ≤ 1 / N := by sorry

end KarpLiptonOM
