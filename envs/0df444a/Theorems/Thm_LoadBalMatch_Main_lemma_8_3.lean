-- Prove2me | Theorems.Thm_LoadBalMatch_Main_lemma_8_3
-- name    : LoadBalMatch.Main.lemma_8_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:34:46.006993+00:00
-- url     : https://prove2.me/theorems/8df07cd3-efe9-4d8f-9e96-9661895a9acd
-- title:
--   Lemma 8.3 — at most $2\log(n)/\delta$ high-mass iterations (false as printed when $\mu(G)=0$)
-- statement:
--   Let $G$ be a graph on the finite set $V$ with $n=|V|$, $\sigma$ an edge stream of $G$, $0<\varepsilon<1$, $\delta=\sqrt{\log_2 n}\cdot\varepsilon$ and $x^\star$ a balanced fractional matching of $G$. Run Algorithm 4 with any admissible choices of $H^{(1)},x^{(1)}$ and, in every iteration, of $M^{(t)}$, $T^{(t)}$ and $x^{(t+1)}$, and with samples $R^{(t)}$ each of positive probability given the past. An iteration $t$ is high-mass if $\sum_{e\in F(x^{(t)})}x^\star_e\ge\delta\,\mu(G)$. Then, among the first $k$ iterations, for every $k$,
--   $$\#\{t\le k:\ t \text{ is high-mass}\}\ \le\ \frac{2\log_2 n}{\delta}.$$
--
--   This caps the number of iterations in which sampling, rather than the external matching, must make progress. As printed the statement fails when $\mu(G)=0$, where every iteration is high-mass ($0\ge\delta\cdot0$); this is recorded as a finding and the lemma is stated as printed.
--
--   Differences from the source:
--   - generalization: the iterations of Algorithm 4 (⌈1026·√log n/ε⌉ of them), x^(t+1) succinct → the first k iterations for every k, of every run with positive-probability samples, for every admissible choice rule; x^(t+1) any balanced fractional matching on the stabilized graph; reason: the proof does not use the iteration count or succinctness; Algorithm 4's runs are instances
--   - reading: log(n) in δ and in 2 log(n)/δ; x⋆ fixed balanced fractional matching of G → Real.logb 2; any balanced x⋆ of G; reason: doublings from 1/n reach 1 after ⌈log₂ n⌉ steps (proof of Lemma 5.3); the statement is made for every choice of x⋆
--   - encoding: Algorithm 4 and its random samples → Alg4Choices with Admissible, histories of samples, InSupport; reason: the process of the paper with all non-random choices adversarial
--   - encoding: a graph G = (V, E) with n = |V| → a SimpleGraph on a finite type V, edges as Sym2 V, n = Fintype.card V; reason: Lean convention; same instances
-- source:
--   Assadi, Bernstein, Wrzos-Kaminska, Better Bounds for Semi-Streaming Maximum Matching via Load Balancing, STOC 2027 submission (sha256 7cd28a8b…), p. 46, Lemma 8.3

import Mathlib
import Definitions.Def_LoadBalMatch_Main_Matching
import Definitions.Def_LoadBalMatch_Main_FracMatching
import Definitions.Def_LoadBalMatch_Main_Algorithm4

namespace LoadBalMatch.Main

theorem lemma_8_3 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (σ : List (Sym2 V)) (hσ : IsEdgeStream G σ) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (P : Alg4Choices V) (hP : P.Admissible G σ) (xs : Sym2 V → ℝ) (hxs : IsBalanced G xs)
    (hs : List (Finset (Sym2 V))) (hhs : P.InSupport G hs) :
    (P.highCount G xs (delta (Fintype.card V) ε) hs : ℝ) ≤
      2 * Real.logb 2 (Fintype.card V) / delta (Fintype.card V) ε := by sorry

end LoadBalMatch.Main
