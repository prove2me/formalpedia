-- Prove2me | Theorems.Thm_LoadBalMatch_Main_lemma_8_5
-- name    : LoadBalMatch.Main.lemma_8_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:35:00.590679+00:00
-- url     : https://prove2.me/theorems/698dc1fc-0e8a-4252-be22-6d2922e34384
-- title:
--   Lemma 8.5 — after $1024\delta/\varepsilon^2$ low-mass iterations, $\Phi\le\varepsilon^2\mu(G)$
-- statement:
--   Let $G$ be a graph on the finite set $V$ with $n=|V|$, $\sigma$ an edge stream of $G$, $0<\varepsilon<1$, $\delta=\sqrt{\log_2 n}\cdot\varepsilon$ and $x^\star$ a balanced fractional matching of $G$. Run Algorithm 4 with any admissible choices and samples of positive probability, and let $N(t)$ be the number of low-mass iterations among the first $t$ (iteration $s$ is low-mass if $\sum_{e\in F(x^{(s)})}x^\star_e<\delta\,\mu(G)$). Then for every $t\ge1$,
--   $$N(t)\ \ge\ \frac{1024\,\delta}{\varepsilon^2}\quad\Longrightarrow\quad \Phi_{t+1}=\eta(x^{(t+1)})-\eta(G)\ \le\ \varepsilon^2\,\mu(G).$$
--
--   Together with Lemma 8.3 and Lemma 7.10 this gives the output guarantee of Theorem 3 after $1026\sqrt{\log n}/\varepsilon$ iterations.
--
--   Differences from the source:
--   - reading: After 1024δ/ε² low-mass iterations, it holds that Φ_t ≤ ε²·µ(G) → for every t ≥ 1 with N(t) ≥ 1024δ/ε², Φ_{t+1} ≤ ε²µ(G); reason: the proof's conclusion (1/Φ_{t+1} ≥ 1/(ε²µ(G)) when N(t) ≥ 1024δ/ε²)
--   - generalization: the iterations of Algorithm 4 with succinct x^(t+1) → every t, every run with positive-probability samples, every admissible choice rule; x^(t+1) any balanced fractional matching on the stabilized graph; reason: the proof uses neither the iteration count nor succinctness
--   - reading: log(n) in δ; x⋆ fixed balanced fractional matching of G → Real.logb 2; any balanced x⋆ of G; reason: log is base 2 in δ (Definition 8.2, the count 1026√log n/ε); the statement is made for every choice of x⋆
--   - encoding: a graph G = (V, E) with n = |V| → a SimpleGraph on a finite type V, edges as Sym2 V, n = Fintype.card V; reason: Lean convention; same instances
-- source:
--   Assadi, Bernstein, Wrzos-Kaminska, Better Bounds for Semi-Streaming Maximum Matching via Load Balancing, STOC 2027 submission (sha256 7cd28a8b…), p. 47, Lemma 8.5

import Mathlib
import Definitions.Def_LoadBalMatch_Main_Matching
import Definitions.Def_LoadBalMatch_Main_FracMatching
import Definitions.Def_LoadBalMatch_Main_Algorithm4

namespace LoadBalMatch.Main

theorem lemma_8_5 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (σ : List (Sym2 V)) (hσ : IsEdgeStream G σ) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (P : Alg4Choices V) (hP : P.Admissible G σ) (xs : Sym2 V → ℝ) (hxs : IsBalanced G xs)
    (hs : List (Finset (Sym2 V))) (hhs : P.InSupport G hs) (hlen : 1 ≤ hs.length)
    (hN : 1024 * delta (Fintype.card V) ε / ε ^ 2 ≤
      (P.lowCount G xs (delta (Fintype.card V) ε) hs : ℝ)) :
    eta (P.xAt hs) - etaOpt G ≤ ε ^ 2 * (matchingNumber G : ℝ) := by sorry

end LoadBalMatch.Main
