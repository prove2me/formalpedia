-- Prove2me | Theorems.Thm_NashOrTriangle_Supplement_theorem_5_1
-- name    : NashOrTriangle.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:50:42.905568+00:00
-- url     : https://prove2.me/theorems/b904c922-f45c-4743-a33d-ec7358b1a8e7
-- title:
--   Theorem 5.1 — games of $\mathbb F_2$ rank $\le r$: a $1/k$-gap pair in time $\mathrm{poly}(r,k)$ with probability $3/4$, and in expected $\mathrm{poly}(r,k)$ time
-- statement:
--   **Theorem 5.1.** Consider countable binary games whose $\mathbb F_2$ rank is at most $r$, accessed through a utility oracle and fixed (oblivious) exact best-response oracles, and let $k\ge2$. There is a universal constant $C$ and the following two randomized algorithms, which receive $r$ and $k$ as input.
--
--   1. A Monte Carlo algorithm that, for every outcome of its random bits, halts within time $(r+k)^C$, operating on numbers of bit length at most $(r+k)^C$, and returns either finite rational mixtures $(p,q)$ of known strategies with
--   $$D(p,q)=U(q)-L(p)\le\frac1k,$$
--   or a report of failure; the probability that it does not return such a pair is at most $1/4$.
--   2. A Las Vegas algorithm that, with probability one, halts with finite rational mixtures $(p,q)$ with $D(p,q)\le1/k$, operating on numbers of bit length at most $(r+k)^C$, and whose expected running time is at most $(r+k)^C$.
--
--   Here $U$ and $L$ are computed in the full game. The theorem says that the open question whether $\mathrm{NorT}(k,t)$ admits a polynomial randomized algorithm has a positive answer under bounded $\mathbb F_2$ rank, a promise that excludes $(r+1)$-triangles.
--
--   **Formalization Note** The algorithms are programs of the published oracle machine with rational literals, reading $r$, $k$ and an infinite sequence of fair random bits from memory. Time is the number of executed instructions, oracle calls included; a polynomial in $r$ and $k$ is written $(r+k)^C$. The failure probability is the outer measure of the set of bad random sequences, and the expectation is taken of the running time, which is $+\infty$ on non-halting runs and is asserted to be measurable.
--
--   Differences from the source:
--   - encoding: a randomized algorithm given integers r ≥ 0 and k ≥ 2 → a LiteralProgram of the published oracle machine on inputRK r k ω, with ω ∼ coinMeasure (independent fair bits); reason: the published model; the proof samples its perturbations from fair random bits
--   - reading: utility and BR oracles → exact and oblivious BRAdversary M 0; reason: the proof uses exact best-response queries ('All four optimizations are legal exact best-response queries') and fixed response maps ('Because the response maps are fixed')
--   - reading: in time polynomial in r and k → work ≤ (r + k)^C and bits ≤ (r + k)^C for one universal C; reason: time counts every instruction and oracle call; the bit-length bound makes a unit-cost step an operation on numbers of polynomial size, as the proof states (O(log(H + LR + 1)) bits); for k ≥ 2 every polynomial in r, k is below some (r + k)^C
--   - reading: returns with probability at least 3/4 a pair with D ≤ 1/k, or reports failure with probability at most 1/4 → for every ω the run halts within the time bound with IsPairAnswer at 1/k or a failure report (tag 2), and the outer measure of the ω that do not yield IsPairAnswer is ≤ 1/4; reason: the algorithm returns one of the two outcomes on every run; outer measure makes the probability bound independent of measurability
--   - encoding: returns a pair with D ≤ 1/k in expected time polynomial in r and k → almost surely halts with IsPairAnswer at 1/k (and the bit bound), haltWork (⊤ if no halt) is measurable, and its lower integral is ≤ (r + k)^C; reason: expected time of a run that may not halt is an extended-valued expectation; measurability makes the lintegral the expectation
--   - encoding: F2 rank at most r of a countable game → F2RankLE: every finite submatrix has rank ≤ r over ZMod 2; reason: the paper: the rank is the supremum of the finite-submatrix ranks
-- source:
--   Daskalakis–Papadimitriou–Yannakakis, On the Complexity of Infinite Zero-Sum Games, STOC 2027 submission (manuscript sha256 4f8d0962cc2efb135d3833e902fa4e861e03acf9d2df3fe8140a50b646da66f7), Theorem 5.1, p.12 (PDF p.13)

import Mathlib
import Definitions.Def_NashOrTriangle_OracleMachine
import Definitions.Def_NashOrTriangle_HaltsWith
import Definitions.Def_NashOrTriangle_IsBinary
import Definitions.Def_NashOrTriangle_IsPairAnswer
import Definitions.Def_NashOrTriangle_Supplement_IsOblivious
import Definitions.Def_NashOrTriangle_Supplement_F2RankLE
import Definitions.Def_NashOrTriangle_Supplement_RandomizedRun

namespace NashOrTriangle.Supplement

open MeasureTheory
open scoped ENNReal

/-- **Theorem 5.1** (a randomized algorithm for games of bounded rank). There is a randomized
algorithm which, given integer `r ≥ 0` and `k ≥ 2`, and utility and BR oracles for a countable
binary game whose `𝔽₂` rank is promised to be at most `r`, returns in time polynomial in `r` and
`k` with probability at least `3/4` finite rational mixtures `(p, q)` with `D(p, q) ≤ 1/k`, or
reports failure with probability at most `1/4`. Under the same promise, there is a randomized
algorithm that returns finite rational mixtures `(p, q)` with `D(p, q) ≤ 1/k` in expected time
polynomial in `r` and `k`.

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), Theorem 5.1, printed p. 12 (PDF p. 13).

**Formalization Note** A randomized algorithm is a program of the published oracle machine with
rational literals only (`LiteralProgram`), run on input memory `inputRK r k ω`, the random bits
`ω` distributed as independent fair coins (`coinMeasure`). The oracles are exact and oblivious
(fixed response maps, as the proof requires: "Because the response maps are fixed"). Time is the
published counter `work` (every executed instruction, oracle calls included), together with the published
counter `bits` (the largest bit length of a number written to a real register), so that a unit-cost
step is an operation on numbers of polynomial bit length, as in the proof ("numerators and
denominators have O(log(H + LR + 1)) bits … polynomial local computation"); "polynomial in `r`
and `k`" is `(r + k)^C` for one universal `C` (for `k ≥ 2` every polynomial in `r` and `k` is
below `(r + k)^C` for a suitable `C`). Part 1: for every `ω` the run halts within that time
(and bit length) with
either a pair of finite rational mixtures of known strategies with `D(p, q) ≤ 1/k` (published
`IsPairAnswer`) or a failure report, and the set of `ω` on which it does not return such a pair
has (outer) measure at most `1/4`. Part 2: the set of `ω` on which the run does not halt with such
a pair (and bit length at most `(r + k)^C`) is null, the running time `haltWork` (`⊤` if the run does not halt) is measurable, and its
expectation is at most `(r + k)^C`. -/
theorem theorem_5_1 :
    (∃ P : Program, LiteralProgram P ∧ ∃ C : ℝ, ∀ r k : ℕ, 2 ≤ k →
      ∀ {A B : Type} [Countable A] [Countable B] [Nonempty A] [Nonempty B] (M : A → B → ℚ),
        IsBinary M → F2RankLE M r → ∀ adv : BRAdversary M 0, IsOblivious adv →
        (∀ ω : ℕ → Bool, HaltsWith P M adv (inputRK r k ω) (fun s =>
            (s.work : ℝ) ≤ ((r : ℝ) + (k : ℝ)) ^ C ∧ (s.bits : ℝ) ≤ ((r : ℝ) + (k : ℝ)) ^ C ∧
            (IsPairAnswer M (1 / (k : ℝ)) s ∨ IsFailureReport s))) ∧
        coinMeasure {ω | ¬ HaltsWith P M adv (inputRK r k ω) (IsPairAnswer M (1 / (k : ℝ)))}
          ≤ 1 / 4) ∧
    (∃ P : Program, LiteralProgram P ∧ ∃ C : ℝ, ∀ r k : ℕ, 2 ≤ k →
      ∀ {A B : Type} [Countable A] [Countable B] [Nonempty A] [Nonempty B] (M : A → B → ℚ),
        IsBinary M → F2RankLE M r → ∀ adv : BRAdversary M 0, IsOblivious adv →
        coinMeasure {ω | ¬ HaltsWith P M adv (inputRK r k ω) (fun s =>
            IsPairAnswer M (1 / (k : ℝ)) s ∧ (s.bits : ℝ) ≤ ((r : ℝ) + (k : ℝ)) ^ C)} = 0 ∧
        Measurable (fun ω => (haltWork P M adv (inputRK r k ω) : ℝ≥0∞)) ∧
        ∫⁻ ω, (haltWork P M adv (inputRK r k ω) : ℝ≥0∞) ∂coinMeasure
          ≤ ENNReal.ofReal (((r : ℝ) + (k : ℝ)) ^ C)) := by sorry

end NashOrTriangle.Supplement
