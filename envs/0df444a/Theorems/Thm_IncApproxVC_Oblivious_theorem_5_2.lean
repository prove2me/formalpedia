-- Prove2me | Theorems.Thm_IncApproxVC_Oblivious_theorem_5_2
-- name    : IncApproxVC.Oblivious.theorem_5_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:44:27.846199+00:00
-- url     : https://prove2.me/theorems/ddfe0556-77a7-417b-b68a-d0a1d2cffbca
-- title:
--   Theorem 5.2 — the incremental threshold max-flow data structure $\mathrm{IncMaxFlow}(s,t,F,U)$: $O(m^{1+o(1)}\operatorname{poly}\log U)$ time and the $1/4$-saturation guarantee
-- statement:
--   There is a data structure $\mathrm{IncMaxFlow}(s,t,F,U)$, initialized with a flow threshold $F\ge 0$, a capacity bound $U\ge 1$ and the network $G'$ with vertices $s,t$ and no edges, which maintains a flow $f$ and supports `InsertVertex`, `InsertEdge`, `GetApproxFlow`, `LowerBoundFlow`, `increaseUpperBound` and `NextModifiedEdge` with the requirements and guarantees of p. 15 (see the definition `IncApproxVC.Oblivious.IncMaxFlow`). Precisely: there are a constant $C>0$, a function $g$ with $g(M)\to 0$ and one program $P$ such that for all $U$, $F$, every coin tape and every operation sequence valid against the run's own answers,
--   $$\text{total work}\ \le\ C\Big(M^{1+g(M)}(1+\log U)^{C}+A+B\Big)+C,\qquad \#\{\text{edges returned by NextModifiedEdge}\}\ \le\ C\,M^{1+g(M)}(1+\log U)^{C}+C,$$
--   where $M$ counts the `InsertVertex`, `InsertEdge`, `LowerBoundFlow` and `increaseUpperBound` calls, $A$ the `GetApproxFlow` calls and $B$ the `NextModifiedEdge` calls. Moreover every run halts, the internal flow respects $l\le f\le u$ after every operation, `GetApproxFlow` is accurate within a factor $1.01$ in residual capacity, `NextModifiedEdge` returns an edge or $\bot$, and on $\bot$ its report on the existence of an $s$–$t$ flow of value at least $F$ is correct and no residual capacity has moved by a factor $1.02$ since the edge was last returned. Finally, at every $\bot$ before success: for every $T\subseteq N^-[t]\setminus\{s\}$ such that $G'$ has an $s$–$T$ flow of value at least $F$, some edge $(v,t)$ with $v\in T\setminus\{t\}$ is at least $1/4$-saturated by $f$.
--
--   This is the paper's re-analysis of the incremental min-cost flow algorithm of Chen, Kyng, Liu, Meierhans and Probst Gutenberg, specialized to max flow, and the engine of Theorem 3.12.
--
--   Differences from the source:
--   - reading: a randomized (or deterministic) incremental algorithm / data structure; no machine is named → one admissible program of the published randomized exact real RAM PNormReg (coin-free for a deterministic algorithm), operations fed online by runOps with the layout of IncApproxVC.Oblivious.Online; reason: the paper names no machine; this is the unit-cost exact real RAM of the published PNormReg_Machine, with free input loading so that local time bounds are meaningful
--   - reading: the internally maintained flow f → f(e) is real cell e of the machine state (a decoding fixed by the mission); reason: 'internally maintains' must be read from the state; a decoding chosen with the program could do unbounded free computation
--   - reading: Across m InsertVertex, InsertEdge and LowerBoundFlow operations, the total running time is O(m^{1+o(1)} poly log U) → total work ≤ C(M^{1+g(M)}(1+log U)^C + A + B) + C with M also counting increaseUpperBound, A = #GetApproxFlow, B = #NextModifiedEdge; reason: read literally, unboundedly many free increaseUpperBound and query calls would be false on any unit-cost machine; poly log U as (1+log U)^C
--   - reading: O(m^{1+o(1)} poly log U) edges returned by NextModifiedEdge → numReturned ≤ C M^{1+g(M)} (1+log U)^C + C; reason: O and o(1) as explicit universal constants and a function g → 0
--   - reading: LowerBoundFlow requires that e has just been returned by NextModifiedEdge() and the f̄ returned by GetApproxFlow → e is the answer of the latest NextModifiedEdge, only GetApproxFlow calls since, the last GetApproxFlow(e) answer is f̄; requirements checked against the run's own answers; reason: the caller is adaptive (Algorithm 2 decides from the answers)
--   - reading: increaseUpperBound(e, u): u an integer larger than u(e); U an upper bound for the capacity of edges → u > current u(e) and u ≤ U; reason: U bounds every capacity (Algorithm 2 sets U = 35 max{p,q}|V|)
--   - reading: At any point in time before NextModifiedEdge has reported success while returning ⊥ (the 1/4-saturation guarantee) → at every return of ⊥ that reports no flow of value F, with no earlier ⊥ reporting one; reason: literally at every point in time it fails for every structure (T = {t} right after an insertion that creates a flow of value F); this is where Lemma 5.5 applies it
--   - reading: an s–T flow routes F(1_s − b) with b ≥ 0 and ‖b(T)‖₁ = 1 → routes F(b − 1_s) with b ≥ 0, b = 0 outside T, Σ_T b = 1 (out of s, into T); reason: sign typo: as printed it is a flow into s, which makes the guarantee vacuous in Algorithm 2's network; the proof of Lemma 5.5 uses flows from s into T
--   - reading: residual capacity has changed by at least a multiplicative factor 1.02 since e′ was last returned → Changed(r_then, r_now): r_then ≠ r_now and one is ≥ 1.02 times the other; reference time = last return of e′, or its insertion if never returned; reason: makes 'since last returned' explicit for never-returned edges and zero residuals
--   - encoding: InsertVertex(v) adds a new vertex v; edges e → vertices numbered 0 = s, 1 = t, then in order of insertion; edges numbered in order of insertion (parallel edges allowed); F real ≥ 0, U natural ≥ 1; reason: names of new objects are fixed by insertion order; same structures
-- source:
--   Adena, Henzinger, Rutschmann, Incremental Approximate Vertex Connectivity via Almost-Linear Time Local Cut Algorithms, STOC 2027 submission (manuscript sha256 d6baac6b…), pp. 14–15, Theorem 5.2

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_IncApproxVC_Oblivious_Flow
import Definitions.Def_IncApproxVC_Oblivious_Online
import Definitions.Def_IncApproxVC_Oblivious_IncMaxFlow

open Filter Topology

namespace IncApproxVC.Oblivious

/-- **Theorem 5.2** (incremental threshold max-flow), pp. 14–15. There are `C > 0`, a function
`g → 0` and one admissible program `P` implementing `IncMaxFlow(s, t, F, U)` such that for every
capacity bound `U ≥ 1`, every flow threshold `F ≥ 0`, every coin tape and every operation sequence
that meets the requirements of p. 15 against the run's own answers (`IncMaxFlow.Valid`; the
sequence may depend on earlier answers), with `M` the number of `InsertVertex`, `InsertEdge`,
`LowerBoundFlow` and `increaseUpperBound` calls, `A` the number of `GetApproxFlow` calls and `B`
the number of `NextModifiedEdge` calls:
* every run halts and the total work is at most `C (M^{1+g(M)} (1 + log U)^C + A + B) + C`;
* the number of edges returned by `NextModifiedEdge` is at most `C M^{1+g(M)} (1 + log U)^C + C`;
* the internally maintained flow (real cell `e` for edge `e`) satisfies `l ≤ f ≤ u` after every
  operation (`FlowFeasible`), `GetApproxFlow` answers within `≈_{1.01}` in residual capacity
  (`ApproxOK`), `NextModifiedEdge` returns an edge or `⊥` (`NMEAnswerOK`), its report on `⊥` is
  correct (`ReportOK`), on `⊥` no residual capacity has moved by a factor `1.02` since the edge was
  last returned (`StableOK`), and the `1/4`-saturation guarantee holds at every `⊥` before success
  (`SaturationOK`). -/
theorem theorem_5_2 :
    ∃ C : ℝ, 0 < C ∧ ∃ g : ℕ → ℝ, Tendsto g atTop (𝓝 0) ∧
      ∃ P : PNormReg.Program, PNormReg.Admissible P ∧
        ∀ U : ℕ, 1 ≤ U → ∀ F : ℝ, 0 ≤ F → ∀ ω : ℕ → Bool, ∀ ops : List IncMaxFlow.Op,
          let M : ℕ := IncMaxFlow.numModifying ops
          let poly : ℝ := (M : ℝ) ^ (1 + g M) * (1 + Real.log U) ^ C
          let T : ℝ := C * (poly + IncMaxFlow.numGetApprox ops + IncMaxFlow.numNext ops) + C
          IncMaxFlow.Valid P ω ⌊T⌋₊ U F ops →
            (∀ k, k ≤ ops.length → (IncMaxFlow.state P ω ⌊T⌋₊ U F ops k).halted = true) ∧
            ((IncMaxFlow.state P ω ⌊T⌋₊ U F ops ops.length).work : ℝ) ≤ T ∧
            (IncMaxFlow.numReturned P ω ⌊T⌋₊ U F ops : ℝ) ≤ C * poly + C ∧
            IncMaxFlow.FlowFeasible P ω ⌊T⌋₊ U F ops ∧
            IncMaxFlow.ApproxOK P ω ⌊T⌋₊ U F ops ∧
            IncMaxFlow.NMEAnswerOK P ω ⌊T⌋₊ U F ops ∧
            IncMaxFlow.ReportOK P ω ⌊T⌋₊ U F ops ∧
            IncMaxFlow.StableOK P ω ⌊T⌋₊ U F ops ∧
            IncMaxFlow.SaturationOK P ω ⌊T⌋₊ U F ops := by sorry

end IncApproxVC.Oblivious
