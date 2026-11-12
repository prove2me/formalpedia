-- Prove2me | Theorems.Thm_NetUnrelEst_Main_theorem_1_1
-- name    : NetUnrelEst.Main.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T07:15:30.526614+00:00
-- url     : https://prove2.me/theorems/7b73e31e-eb03-4770-8548-b483edb341bb
-- title:
--   Theorem 1.1 — an unbiased (1 ± ε)-approximation of network unreliability with failure probability δ in expected time O(m log² n ε⁻² log(1/δ))
-- statement:
--   The input is a connected undirected multigraph $G$ with $n\ge2$ vertices and $m$ edges, where edge $e$ fails independently with probability $p_e\in[0,1]$. Its unreliability $u$ is the probability that the working edges leave $G$ disconnected. For $0<\varepsilon,\delta<1/2$, there is an algorithm that returns $\hat u\ge0$ satisfying
--   $$\mathbb E\hat u=u,\qquad \Pr\big(|\hat u-u|>\varepsilon u\big)\le\delta,$$
--   in expected time
--   $$O\big(m\log^2 n\ \varepsilon^{-2}\log(1/\delta)\big).$$
--
--   This is the near-linear-time unreliability estimator conjectured by Karger. Since reading the input takes $\Omega(m)$ time, it is optimal up to the factor $\log^2 n$ for fixed $\varepsilon$ and $\delta$. Unlike the earlier almost-linear algorithms, it uses no maximum-flow computation.
--
--   **Formalization Note.** There are $C>0$, a word-size constant $c_w$ and one admissible program $P$ of the randomized real RAM with capped word instructions, all fixed before the input. For every input and every word size $W\ge c_w\lceil\log_2(n+m+2)\rceil$, $P$ reads $n,m,W$ and the endpoints from integer memory and $\varepsilon,\delta,p_1,\dots,p_m$ from real memory; it is never given $u$. Then:
--   - every halting run outputs $\hat u\ge0$ in real output cell $0$;
--   - $\hat u$ ($0$ on a non-halting run) is integrable under the uniform tape law, with integral $u$;
--   - the tape measure of the runs that do not halt with $|\hat u-u|\le\varepsilon u$ is at most $\delta$;
--   - the expected work, a lintegral that is $\infty$ on non-halting runs, is at most $C\,m(\log n)^2\varepsilon^{-2}\log(1/\delta)$, with $n$ the input vertex count.
--
--   Differences from the source:
--   - reading: 'there is an algorithm … in expected time' (no machine named) → one admissible program of the published randomized real RAM (no floor, no real-to-integer conversion, no graph-level instruction) extended by unit-cost word instructions capped at 2^W, for every word size W ≥ c_w⌈log₂(n + m + 2)⌉ given in the input; reason: the paper's algorithm uses machine words (App. G.3.2 bit masks, Corollary G.5) on a unit-cost randomized RAM; the transdichotomous word size is the standard convention
--   - encoding: O(m log² n ε⁻² log(1/δ)) → ∃ C > 0 quantified before every input: expected work ≤ C·m·(log n)²·ε⁻²·log(1/δ); reason: the meaning of O(·), uniform over inputs; the expression is bounded below by a positive constant on the domain, so no additive constant is needed
--   - encoding: Eû = u and Pr(|û − u| > εu) ≤ δ → û (0 on non-halting runs) integrable with integral u; the measure of the runs that do not halt with |û − u| ≤ εu is ≤ δ; û ≥ 0 on every halting run; reason: non-halting runs count as failures, so the bound is at least as strong as the paper's; the measure of a failure set avoids an outer-measure complement
--   - generalization: a connected undirected graph with parallel edges allowed → a connected map Fin m → Fin n × Fin n, so self-loops are also allowed; reason: the reduction of §2.1 discards self-loops, so the algorithm handles them; the paper's inputs are the loop-free instances
-- source:
--   Sun, Near-Linear Estimation of Network Unreliability, STOC 2027 submission, doi:10.5281/zenodo.23913531 (PDF sha256 eee2585a…), p. 3, Theorem 1.1

import Mathlib
import Definitions.Def_NetUnrelDesign_Main_Model
import Definitions.Def_NetUnrelDesign_Main_Machine
import Definitions.Def_NetUnrelEst_Main_CutSums
import Definitions.Def_NetUnrelEst_Main_WordMachine

open scoped BigOperators ENNReal

open NetUnrelDesign.Main

namespace NetUnrelEst.Main

/-- **Theorem 1.1.** There are a constant `C > 0`, a word-size constant `c_w` and one admissible
program `P` of the randomized real RAM with capped word instructions such that, for every
connected multigraph with `n ≥ 2` vertices and `m` edges, every `p ∈ [0,1]^m`, every
`0 < ε, δ < 1/2` and every word size `W ≥ c_w ⌈log₂(n + m + 2)⌉`, the program, given the graph,
`W`, `ε`, `δ` and `p` (not `u`), returns `û ≥ 0` on every halting run, with `Eû = u`,
`Pr(|û − u| > εu) ≤ δ` (non-halting runs count as failures), and expected work at most
`C m log² n ε⁻² log(1/δ)`. Sun 2027, p. 3, Theorem 1.1. -/
theorem theorem_1_1 :
    ∃ C : ℝ, 0 < C ∧ ∃ cw : ℕ, ∃ P : WProgram, WAdmissible P ∧
      ∀ {n m : ℕ} (ends : Ends n m), 2 ≤ n → IsConnectedGraph ends →
        ∀ p : Fin m → ℝ, (∀ e, 0 ≤ p e ∧ p e ≤ 1) →
        ∀ ε δ : ℝ, 0 < ε → ε < 1 / 2 → 0 < δ → δ < 1 / 2 →
        ∀ W : ℕ, cw * Nat.clog 2 (n + m + 2) ≤ W →
          wOnEveryHalt W P (initState noOracle (graphInts W ends) ([ε, δ] ++ List.ofFn p))
              (fun s => 0 ≤ outReal s 0) ∧
          MeasureTheory.Integrable
              (wOutput W P (initState noOracle (graphInts W ends) ([ε, δ] ++ List.ofFn p)))
              jointLaw ∧
          ∫ ω, wOutput W P (initState noOracle (graphInts W ends) ([ε, δ] ++ List.ofFn p)) ω
              ∂jointLaw = unrel ends p ∧
          wFailureProb W P (initState noOracle (graphInts W ends) ([ε, δ] ++ List.ofFn p))
              (fun s => |outReal s 0 - unrel ends p| ≤ ε * unrel ends p) ≤ ENNReal.ofReal δ ∧
          wExpectedWork W P (initState noOracle (graphInts W ends) ([ε, δ] ++ List.ofFn p)) ≤
            ENNReal.ofReal (C * m * Real.log n ^ 2 * ε⁻¹ ^ 2 * Real.log (1 / δ)) := by sorry

end NetUnrelEst.Main
