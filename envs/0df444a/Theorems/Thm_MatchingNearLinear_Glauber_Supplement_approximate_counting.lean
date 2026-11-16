-- Prove2me | Theorems.Thm_MatchingNearLinear_Glauber_Supplement_approximate_counting
-- name    : MatchingNearLinear.Glauber.Supplement.approximate_counting
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:00:06.426209+00:00
-- url     : https://prove2.me/theorems/b553290e-780e-476d-8e90-765a6db60bc6
-- title:
--   Theorem 1.3 — Fast approximate counting
-- statement:
--   Fix $\lambda_{\max}>0$. There are a randomized sequential program $A$ (the random-choice RAM: a single processor), a word-capacity exponent $r$, an exponent $k$ and a constant $C>0$, depending only on $\lambda_{\max}$, with the following property. Let $G$ be a simple graph with $n\ge1$ vertices and $m\ge0$ edges and maximum matching size $\nu(G)$, let $0<\lambda_e\le\lambda_{\max}$ and $0<\varepsilon\le1/2$, put $Z_G(\lambda)=\sum_M\prod_{e\in M}\lambda_e$ (sum over matchings) and $L=\log(2+n+m+1/\varepsilon)$. Run $A$ on the edge list of $G$ with $\lambda$ and $\varepsilon$, with words below $(n+m+\lceil1/\varepsilon\rceil+2)^{r+1}$. Then on every run $A$ halts with a real output $\hat Z$ and work at most
--   $$C\Big(m+n+\frac{\nu(G)^2}{\varepsilon^2}\Big)L^k\qquad\text{and at most}\qquad C\,\frac{n^2}{\varepsilon^2}\,L^k,$$
--   and
--   $$\Pr\big[(1-\varepsilon)Z_G(\lambda)\le\hat Z\le(1+\varepsilon)Z_G(\lambda)\big]\ \ge\ \frac34 .$$
--
--   So the monomer–dimer partition function is approximated within relative error $\varepsilon$ with probability at least $3/4$ using $\tilde O_{\lambda_{\max}}(m+n+\nu(G)^2/\varepsilon^2)$, hence $\tilde O_{\lambda_{\max}}(n^2/\varepsilon^2)$, work on every run.
--
--   Differences from the source:
--
--   - encoding: randomized algorithm in the random-choice RAM with unit-cost arithmetic, comparisons, exact uniform choices and Bernoulli draws → a sequential (spawn-free) CREW.Program on the closed-instruction-set machine with words below (n+m+⌈1/ε⌉+2)^(r+1); work = executed instructions; reason: the §2.3 model made operational
--   - encoding: Õ_{λmax}(·) → C·(·)·(log(2+n+m+1/ε))^k with C>0 and k chosen from λmax alone, before every instance; reason: definition of Õ after Theorem 1.2 (printed p. 2)
--   - encoding: a simple graph with n vertices → a labeled simple graph with n ≥ 1 vertices; reason: the vertex-free input has empty bounds Õ(n²/ε²) = 0 that no halting program meets, so the statement concerns graphs with vertices; every other instance is kept, including m = 0
--   - encoding: probability of the event for the returned Ẑ → product measure of the randomness sequences whose run halts with output Ẑ in the interval; reason: push-forward of the random choices
-- source:
--   Tianshun Miao, Yitong Yin, Sampling Matchings in Near-linear Time, STOC 2027 submission #444 (October 2026), Theorem 1.3, printed p. 3 (PDF p. 5); computational model §2.3, printed p. 9 (PDF p. 11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/444.pdf

import Mathlib
import Definitions.Def_MatchingNearLinear_Glauber_Supplement_Programs

set_option autoImplicit false

namespace MatchingNearLinear.Glauber.Supplement

open MatchingNearLinear.Glauber

/-- Tianshun Miao and Yitong Yin, Sampling Matchings in Near-linear Time,
STOC 2027 submission #444 (October 2026). Exact result and pages in the item metadata. -/
theorem approximate_counting :
    ∀ lmax : ℝ, 0 < lmax → ∃ (A : CREW.Program) (r k : ℕ) (C : ℝ), 0 < C ∧ A.Sequential ∧
      ∀ (n m : ℕ), 1 ≤ n → ∀ (G : Input n m) (lam : Fin m → ℝ), ActivityBound lam lmax →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1/2 →
        let cap := CREW.capacity (n + m + ⌈1/ε⌉₊) r
        let input := graphInput G lam ε
        let Z := MaxEntOCRS.partitionFn G.graph lam
        let L := Real.log (2 + n + m + 1/ε)
        (∀ ω : CREW.Randomness, ∃ t c x, CREW.HaltsAt A cap input ω t c ∧ OutputsReal c x ∧
          (c.work : ℝ) ≤ C * ((m : ℝ) + n + (maxMatchingSize G : ℝ)^2 / ε^2) * L^k ∧
          (c.work : ℝ) ≤ C * ((n : ℝ)^2 / ε^2) * L^k) ∧
        3/4 ≤ CREW.prob A cap input
          (fun _ c => ∃ x, OutputsReal c x ∧ (1 - ε) * Z ≤ x ∧ x ≤ (1 + ε) * Z) := by sorry

end MatchingNearLinear.Glauber.Supplement
