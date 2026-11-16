-- Prove2me | Theorems.Thm_MatchingNearLinear_Glauber_Supplement_parallel_sampling
-- name    : MatchingNearLinear.Glauber.Supplement.parallel_sampling
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:57:19.872455+00:00
-- url     : https://prove2.me/theorems/e5d011d8-b7ee-4561-a75e-a4cf33fabb3b
-- title:
--   Theorem 1.2 — Work-efficient parallel sampling
-- statement:
--   Fix $\lambda_{\max}>0$. There are a randomized CREW PRAM program $A$, a word-capacity exponent $r$, an exponent $k$ and a constant $C>0$, depending only on $\lambda_{\max}$, with the following property. Let $G$ be a simple graph with $n$ vertices, $m\ge1$ edges, maximum degree $\Delta$ and maximum matching size $\nu(G)$; let $0<\lambda_e\le\lambda_{\max}$ be edge activities and $0<\varepsilon\le1/2$; and put $L=\log\frac{n+m}{\varepsilon}$. Run $A$ on the edge list of $G$ with $\lambda$ and $\varepsilon$, with words below $(n+m+\lceil1/\varepsilon\rceil+2)^{r+1}$.
--
--   1. On every run, $A$ halts, outputs a matching of $G$, and performs work at most $C(m+n)L^k$.
--   2. Its output law $\hat\mu$ is a probability distribution with $d_{TV}(\hat\mu,\mu_{G,\lambda})\le\varepsilon$.
--   3. For every $c>0$ there is $C_c>0$, depending only on $\lambda_{\max}$ and $c$, such that
--   $$\Pr\Big[\operatorname{depth}\le C_c\,\min\{\Delta,\sqrt{\nu(G)}\}\,L^k\Big]\ \ge\ 1-\min\{1/4,\,n^{-c}\}.$$
--
--   So a random matching within total-variation distance $\varepsilon$ of the monomer–dimer law is produced with $\tilde O_{\lambda_{\max}}(m+n)$ work on every run and, with high probability, $\tilde O_{\lambda_{\max}}(\min\{\Delta,\sqrt{\nu(G)}\})$ depth.
--
--   **Formalization Note** The machine is the closed-instruction-set randomized CREW PRAM of the supplement's CREW definition; work counts executed instructions and depth counts synchronous steps.
--
--   Differences from the source:
--
--   - encoding: randomized CREW PRAM, work = total operations, depth = longest dependency chain → a CREW.Program on the closed-instruction-set synchronous machine with exclusive writes and words below (n+m+⌈1/ε⌉+2)^(r+1); work = executed instructions, depth = steps until halting; reason: the §2.3 model made operational; a synchronous PRAM step count is its dependency depth
--   - encoding: Õ_{λmax}(·): polylogarithmic factors in graph size and 1/ε, constants depending on λmax → C·(·)·(log((n+m)/ε))^k with C>0 and k chosen from λmax alone, before every graph, activity and ε; reason: definition of Õ after Theorem 1.2 (printed p. 2); log n, log(n+m) and log(n/ε) agree up to constants since m ≤ n²
--   - reading: with high probability → for every c>0 a constant C_c with probability at least 1 − min{1/4, n^(−c)}; the program does not depend on c; reason: the proof of Theorem 1.2 (printed p. 27) applies Theorem 5.1 with η = min{1/4, n^(−c)} for any fixed c>0
--   - encoding: distribution μ̂ of the returned matching → probability of each output under the product of uniform laws driving the random primitives, with the conjunct that these probabilities form a distribution; reason: push-forward of the random choices; a program halting on every run has a distribution as output law
-- source:
--   Tianshun Miao, Yitong Yin, Sampling Matchings in Near-linear Time, STOC 2027 submission #444 (October 2026), Theorem 1.2, printed p. 2 (PDF p. 4); with high probability as instantiated in the proof of Theorem 1.2, printed p. 27 (PDF p. 29); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/444.pdf

import Mathlib
import Definitions.Def_MatchingNearLinear_Glauber_Supplement_Programs

set_option autoImplicit false

namespace MatchingNearLinear.Glauber.Supplement

open MatchingNearLinear.Glauber

/-- Tianshun Miao and Yitong Yin, Sampling Matchings in Near-linear Time,
STOC 2027 submission #444 (October 2026). Exact result and pages in the item metadata. -/
theorem parallel_sampling :
    ∀ lmax : ℝ, 0 < lmax → ∃ (A : CREW.Program) (r k : ℕ) (C : ℝ), 0 < C ∧
      (∀ (n m : ℕ), 1 ≤ m → ∀ (G : Input n m) (lam : Fin m → ℝ), ActivityBound lam lmax →
        ∀ ε : ℝ, 0 < ε → ε ≤ 1/2 →
        let cap := CREW.capacity (n + m + ⌈1/ε⌉₊) r
        let input := graphInput G lam ε
        (∀ ω : CREW.Randomness, ∃ t c S, CREW.HaltsAt A cap input ω t c ∧
          OutputsConfig m c S ∧ EdmondsMatching65.Polyhedron.IsMatching G.graph S ∧
          (c.work : ℝ) ≤ C * ((m : ℝ) + n) * (Real.log (((n : ℝ) + m) / ε))^k) ∧
        MarkovMixing.IsDist (configLaw A cap input m) ∧
        totalVariation (configLaw A cap input m) (matchingLaw G lam) ≤ ε) ∧
      (∀ c : ℝ, 0 < c → ∃ Cc : ℝ, 0 < Cc ∧
        ∀ (n m : ℕ), 1 ≤ m → ∀ (G : Input n m) (lam : Fin m → ℝ), ActivityBound lam lmax →
        ∀ ε : ℝ, 0 < ε → ε ≤ 1/2 →
        1 - min (1/4 : ℝ) ((n : ℝ) ^ (-c)) ≤
          CREW.prob A (CREW.capacity (n + m + ⌈1/ε⌉₊) r) (graphInput G lam ε)
            (fun t _ => (t : ℝ) ≤ Cc * min (maxDegree G : ℝ) (Real.sqrt (maxMatchingSize G)) *
              (Real.log (((n : ℝ) + m) / ε))^k)) := by sorry

end MatchingNearLinear.Glauber.Supplement
