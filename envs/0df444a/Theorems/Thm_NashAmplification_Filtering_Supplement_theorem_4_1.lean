-- Prove2me | Theorems.Thm_NashAmplification_Filtering_Supplement_theorem_4_1
-- name    : NashAmplification.Filtering.Supplement.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:59:19.358991+00:00
-- url     : https://prove2.me/theorems/c3e548a5-54cb-476b-a1be-c1a92eb95866
-- title:
--   Theorem 4.1 — running-time transfer between δ-ANE and (ε, η)-weak ANE
-- statement:
--   Fix an integer $k\ge2$ and real parameters $\delta,\varepsilon\in(0,1)$, $\eta\in[0,1)$. Then there are integers $C\ge2$ and $a_0,b_0\ge1$, and a polynomial-time construction mapping each $k$-player game $G$ with payoffs in $[0,1]$ to a symmetric binary-payoff $C$-player game, all depending only on $k,\delta,\varepsilon,\eta$, with the following guarantees. Write $M$ for the encoding length of an input game and $N$ for that of a target game. Let the *target promise* be either (a) all symmetric binary-payoff $C$-player games, or (b) only the constructed games. For each of the two promises:
--
--   1. **Upper transfer (4.1).** Let $S$ be a nondecreasing running-time bound on $(0,\infty)$. If a deterministic algorithm finds an $(\varepsilon,\eta)$-weak approximate Nash equilibrium of every promised game in time $S(N)$, then a deterministic algorithm finds a $\delta$-approximate Nash equilibrium of every $k$-player game with payoffs in $[0,1]$ in time
--   $$O\big((M+S(M^{b_0}))^{a_0}\big).$$
--   2. **Lower transfer (4.2)–(4.3).** Let $T$ be nondecreasing on $(0,\infty)$. Suppose no deterministic algorithm for the $\delta$-ANE problem on $k$-player games runs in time $o(T(M))$, and
--   $$M^{a_0}=o(T(M)).$$
--   Then no deterministic algorithm for the weak-ANE problem on the promised games runs in time $o(T'(N))$, where
--   $$T'(N)=\big[T\big(N^{1/b_0}\big)\big]^{1/a_0}.$$
--
--   Here an algorithm is a fixed deterministic multi-stack Turing machine that reads the complete encoded payoff table and writes the explicit encoded rational profile; running time counts all steps including output. A time bound at a real argument $L$ covers every promised input of length at most $L$. The functions $S$ and $T$ are arbitrary nondecreasing functions, with no polynomial, continuity or constructibility assumption, and no complexity conjecture is assumed.
--
--   This companion theorem turns the construction-and-recovery reduction of the goal into quantitative running-time transfers in both directions; the paper uses it to derive its polynomial-time equivalence and PPAD-ETH consequences.
--
--   Differences from the source:
--   - reading: the constructed games (of the construction of Theorem 1.1) → the range of an existential map construct, fixed with C, a0, b0 before S, T and every solver, that is TM2-polynomial-time computable and outputs symmetric binary-payoff C-player tables; reason: the source's construction is the one of Theorem 1.1, which has exactly these properties; the Lean statement asserts the transfer for some such construction, which the source's construction witnesses
--   - encoding: a deterministic algorithm running in time S(N), O(·), o(·); bounds nondecreasing, applied to inputs of length at most their argument and extended to positive reals → a FinTM2 machine whose step count m on each promised input satisfies m ≤ B(L) for every real L ≥ the input length, with Big-O / little-o of B at Filter.atTop on ℝ; S and T are MonotoneOn (0,∞); reason: this is the source's stated convention; FinTM2 steps and bit operations are polynomially related, an overhead the existential a0 absorbs
--   - encoding: finds an (ε, η)-weak ANE / δ-ANE, with explicit rational output → halts with encProfile σ on the output stack for a σ satisfying IsWeakANEOf / IsDeltaANEOf; reason: uses the base mission's published encodings and equilibrium predicates; writing the output is charged to the step count
--   - encoding: both conclusions also hold when the algorithm is guaranteed only on the constructed games → both conclusions are stated for each of the two promises P = IsSymBinaryTable C and P = range construct; reason: the two clauses for each promise are exactly the source's two conclusions and its final sentence
-- source:
--   Deng, Li, Wang and Zhang, Hardness Amplification for Approximate Nash Equilibrium with a Constant Number of Players, STOC 2027 submission #120 (October 2026), SHA-256 c201a27da9b9920a924945f1a30c7919ae6b922c99430223ee9bbcdec5b0ffa8, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/120.pdf, Theorem 4.1 and (4.1)–(4.3), PDF p. 23 (printed p. 22); running-time convention of §4.1, PDF p. 22 (printed p. 21)

import Definitions.Def_NashAmplification_Filtering_Supplement_Solvers

open scoped BigOperators
noncomputable section

namespace NashAmplification.Filtering.Supplement
open OnlineCRS.Combine

/-- Theorem 4.1 (Running-time transfer), PDF 23 (printed 22). `C`, `a₀`, `b₀` and the fixed
construction precede every running-time bound, solver and game. For each target promise — all
symmetric binary-payoff `C`-player games, or only the constructed games — both the upper
transfer (4.1) and the lower transfer (4.2)–(4.3) hold. -/
theorem theorem_4_1 (k : ℕ) (hk : 2 ≤ k) (δ ε η : ℝ)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) (hε : ε ∈ Set.Ioo (0 : ℝ) 1)
    (hη : η ∈ Set.Ico (0 : ℝ) 1) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ a₀ b₀ : ℕ, 1 ≤ a₀ ∧ 1 ≤ b₀ ∧
    ∃ construct : Table k → Table C,
      Nonempty (Turing.TM2ComputableInPolyTime encGame encGame construct) ∧
      (∀ G : Table k, IsSymBinaryTable C (construct G)) ∧
      ∀ P : Table C → Prop,
        (P = IsSymBinaryTable C ∨ P = fun H => ∃ G : Table k, construct G = H) →
        -- (4.1): a weak-ANE solver in time `S(N)` gives a δ-ANE solver in `O((M + S(M^b₀))^a₀)`.
        (∀ S : ℝ → ℝ, MonotoneOn S (Set.Ioi 0) →
          ∀ A : Turing.TM2ComputableAux Sym Sym,
            SolvesWithin A encGame P (IsWeakANEOf ε η) S →
            ∃ A' : Turing.TM2ComputableAux Sym Sym,
              SolvesInBigO A' encGame (fun _ : Table k => True) (IsDeltaANEOf δ)
                (fun M : ℝ => (M + S (M ^ b₀)) ^ a₀)) ∧
        -- (4.2)–(4.3): lower-bound transfer with `T′(N) = (T(N^{1/b₀}))^{1/a₀}`.
        (∀ T : ℝ → ℝ, MonotoneOn T (Set.Ioi 0) →
          (∀ A' : Turing.TM2ComputableAux Sym Sym,
            ¬ SolvesInLittleO A' encGame (fun _ : Table k => True) (IsDeltaANEOf δ) T) →
          (fun M : ℝ => M ^ a₀) =o[Filter.atTop] T →
          ∀ A : Turing.TM2ComputableAux Sym Sym,
            ¬ SolvesInLittleO A encGame P (IsWeakANEOf ε η)
              (fun N : ℝ => (T (N ^ ((1 : ℝ) / b₀))) ^ ((1 : ℝ) / a₀))) := by sorry

end NashAmplification.Filtering.Supplement
