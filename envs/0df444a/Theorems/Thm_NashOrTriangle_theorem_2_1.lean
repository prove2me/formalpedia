-- Prove2me | Theorems.Thm_NashOrTriangle_theorem_2_1
-- name    : NashOrTriangle.theorem_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:54:43.330357+00:00
-- url     : https://prove2.me/theorems/78ba0d62-7893-46a1-b6de-7cf65e9ce4a6
-- title:
--   Theorem 2.1 — Nash or Triangle with $2^{O(t^3k^4\log(tk))}$ calls on binary games and $2^{O(t^3k^7\log^5k)}$ on real-valued games
-- statement:
--   There are universal constants $c, c_0 > 0$ and a deterministic algorithm in the oracle model with the following guarantee. Let $k, t \ge 2$, and let $G$ be a countable game with payoffs in $[0,1] \cap \mathbb Q$, accessed with $\delta$-BR oracles (possibly adaptive) for some $0 \le \delta \le c_0/k$.
--
--   1. If $G$ is binary, the algorithm makes at most $2^{O(t^3k^4\log(tk))}$ oracle calls and $2^{O(t^4k^4\log(tk))}$ steps of local computation, each on rationals whose bit length is polynomial in the call bound and in the bit length of the payoffs encountered, and returns either a pair $(p, q)$ with
--   $$
--   D(p, q) \le 1/k
--   $$
--   or a $t$-triangle.
--   2. If $G$ is real-valued, the algorithm makes at most $2^{O(t^3k^7\log^5 k)}$ oracle calls and $2^{O(t^4k^7\log^5 k)}$ steps of local computation (again on rationals of bit length polynomial in the call bound and the payoff bit length), and returns either a pair with $D(p, q) \le 1/k$ or a $(t, c/k)$-triangle.
--
--   Here $D(p,q) = U(q) - L(p)$ is computed in the full game, the pair consists of finite rational mixtures of strategies the algorithm has discovered, and the triangle consists of discovered strategies. This is the paper's main upper bound: Nash or Triangle, unlike its two halves, is solvable in the oracle model, with a number of calls exponential in a polynomial of $k$ and $t$.
--
--   **Formalization Note** One program serves every $k$, $t$, game, $\delta$ and oracle, in both parts; the hidden constants of the four bounds are one universal $C$.
--
--   Differences from the source:
--   - encoding: a deterministic algorithm in the oracle model accessed with δ-BR oracles, against an adaptive adversary → one LiteralProgram of the real pointer machine (SmaleNinth core, rational literals) with utility, BR and halt instructions, run with every BRAdversary (answers indexed by the BR-call count, valid on every finite rational mixture); reason: the paper's model: steps are operations on rationals, strategies are known only through labels; for a fixed deterministic program a call-indexed adversary is as general as a history-dependent one
--   - encoding: oracle calls → utilCalls + brCalls of the halted state; reason: both oracles are counted, as in the paper
--   - encoding: 2^{O(x)} for the four bounds → 2^{C x} with one universal C (Real.rpow); reason: for k, t ≥ 2 every exponent x is at least 1, so 2^{O(x)} and 2^{Cx} agree; log is the natural logarithm, the base being absorbed by C
--   - encoding: steps of local computation → work: every executed instruction, oracle calls and halt included; reason: work is at least the number of local steps, so the stated step bound is at least as strong as the printed one
--   - encoding: "Each step is an arithmetic operation or a comparison on rationals whose bit length is polynomial in the call bound and in the bit length of the payoffs encountered" (paragraph after the theorem) → a third clause in each part: bits ≤ (N · (payBits + 1))^C, with N the call bound of that part, bits the largest bit length of a number written to a real register during the run and payBits the largest bit length of a payoff returned by a utility call; reason: the sentence defines what a step of the local computation is; every operand of an arithmetic operation or comparison is a register value, and since N ≥ 2 every polynomial in N and the payoff bit length is below (N · (payBits + 1))^C for a universal C
--   - encoding: maximizing or minimizing BR queries on ⊥ allowed initially → allowed at any time (a query with count 0); reason: an arbitrary answer to ⊥ is also a valid answer to a query on a point mass of a known strategy, so ⊥ queries give a program no extra power; no instance changes
--   - encoding: G real-valued → ¬ IsBinary M; reason: the paper: "binary if M takes only the values 0 and 1, and real-valued otherwise"
--   - encoding: returns a pair (p, q) or a triangle → halts with an answer decoded from memory (IsNorTAnswerBinary / IsNorTAnswerReal): finite rational mixtures of known labels, or t row and t column labels of known strategies; reason: Definition 1.1: outputs are finitely supported with rational probabilities, and the algorithm names strategies by their labels; the memory layout is a convention
-- source:
--   Daskalakis–Papadimitriou–Yannakakis, On the Complexity of Infinite Zero-Sum Games, STOC 2027 submission (manuscript sha256 4f8d0962…66f7), Theorem 2.1, pp.4–5 (PDF pp.5–6)

import Mathlib
import Definitions.Def_NashOrTriangle_OracleMachine
import Definitions.Def_NashOrTriangle_HaltsWith
import Definitions.Def_NashOrTriangle_IsPayoff
import Definitions.Def_NashOrTriangle_IsBinary
import Definitions.Def_NashOrTriangle_IsNorTAnswerBinary
import Definitions.Def_NashOrTriangle_IsNorTAnswerReal
import Definitions.Def_NashOrTriangle_inputKT

namespace NashOrTriangle

/-- **Theorem 2.1** (Nash or Triangle is solved with exponentially many oracle calls). There are
universal constants `c, c₀ > 0` and a deterministic algorithm in the oracle model with the
following guarantee. Let `k, t ≥ 2`, and let `G` be a countable game with rational entries in
`[0, 1]` accessed with `δ`-BR oracles for some `0 ≤ δ ≤ c₀/k`.
(a) If `G` is binary, the algorithm makes at most `2^{O(t³k⁴ log(tk))}` oracle calls and
`2^{O(t⁴k⁴ log(tk))}` steps of local computation, and returns either a pair `(p, q)` with
`D(p, q) ≤ 1/k` or a `t`-triangle.
(b) If `G` is real-valued, the algorithm makes at most `2^{O(t³k⁷ log⁵ k)}` oracle calls and
`2^{O(t⁴k⁷ log⁵ k)}` steps of local computation, and returns either a pair with `D(p, q) ≤ 1/k`
or a `(t, c/k)`-triangle.

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), Theorem 2.1, printed pp. 4–5 (PDF pp. 5–6).

**Formalization Note** One program `P` (rational literals only) serves every `k`, `t` (input
cells `0`, `1`), every game, every `δ` and every adaptive oracle, in both parts. "Real-valued" is
"not binary". The hidden constant of all four `2^{O(·)}` bounds is one universal `C`; for
`k, t ≥ 2` every exponent is at least `1`, so `2^{O(x)}` is written `2^{C x}`. Oracle calls are
utility plus BR calls; steps of local computation are bounded by `work`, which counts every
executed instruction (the calls included), so the step bound is at least as strong as printed.
The sentence after the theorem, "Each step is an arithmetic operation or a comparison on rationals
whose bit length is polynomial in the call bound and in the bit length of the payoffs
encountered", is stated as a clause: `bits` (the largest bit length of a number the local
computation produced) is at most `(N · (β + 1))^C`, where `N` is the call bound and `β = payBits`
the largest bit length of a payoff returned by a utility call; since `N ≥ 2`, every polynomial in
`N` and `β` is below `(N · (β + 1))^C` for a suitable universal `C`.
The output must name known strategies; `D` is computed in the full game. -/
theorem theorem_2_1 :
    ∃ c c₀ : ℝ, 0 < c ∧ 0 < c₀ ∧ ∃ C : ℝ, ∃ P : Program, LiteralProgram P ∧
      ∀ k t : ℕ, 2 ≤ k → 2 ≤ t →
      ∀ {A B : Type} [Countable A] [Countable B] [Nonempty A] [Nonempty B] (M : A → B → ℚ),
        IsPayoff M → ∀ δ : ℝ, 0 ≤ δ → δ ≤ c₀ / (k : ℝ) → ∀ adv : BRAdversary M δ,
        (IsBinary M → HaltsWith P M adv (inputKT k t) (fun s =>
            ((s.utilCalls + s.brCalls : ℕ) : ℝ) ≤
              (2 : ℝ) ^ (C * (t : ℝ) ^ 3 * (k : ℝ) ^ 4 * Real.log ((t : ℝ) * (k : ℝ))) ∧
            (s.work : ℝ) ≤
              (2 : ℝ) ^ (C * (t : ℝ) ^ 4 * (k : ℝ) ^ 4 * Real.log ((t : ℝ) * (k : ℝ))) ∧
            (s.bits : ℝ) ≤
              ((2 : ℝ) ^ (C * (t : ℝ) ^ 3 * (k : ℝ) ^ 4 * Real.log ((t : ℝ) * (k : ℝ))) *
                ((s.payBits : ℝ) + 1)) ^ C ∧
            IsNorTAnswerBinary M k t s)) ∧
        (¬ IsBinary M → HaltsWith P M adv (inputKT k t) (fun s =>
            ((s.utilCalls + s.brCalls : ℕ) : ℝ) ≤
              (2 : ℝ) ^ (C * (t : ℝ) ^ 3 * (k : ℝ) ^ 7 * Real.log (k : ℝ) ^ 5) ∧
            (s.work : ℝ) ≤
              (2 : ℝ) ^ (C * (t : ℝ) ^ 4 * (k : ℝ) ^ 7 * Real.log (k : ℝ) ^ 5) ∧
            (s.bits : ℝ) ≤
              ((2 : ℝ) ^ (C * (t : ℝ) ^ 3 * (k : ℝ) ^ 7 * Real.log (k : ℝ) ^ 5) *
                ((s.payBits : ℝ) + 1)) ^ C ∧
            IsNorTAnswerReal M k t (c / (k : ℝ)) s)) := by sorry

end NashOrTriangle
