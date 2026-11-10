-- Prove2me | Theorems.Thm_MinSumRadiiPTAS_Main_lemma_6_7
-- name    : MinSumRadiiPTAS.Main.lemma_6_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:06:21.405294+00:00
-- url     : https://prove2.me/theorems/79c2cdbd-7d0e-46b1-b715-20350f98e89d
-- title:
--   Lemma 6.7 — randomized DP on $P''$: radii $\le r_{\max}$ and LMP inequality against $O_{3R}$ w.p. $\ge 1-\varepsilon^2/n^4$, time $N^{2^{C/\varepsilon}}$
-- statement:
--   **Lemma 6.7** (p. 27; proof p. 38). There are one admissible program $P$ of the randomized distance-oracle real RAM and one absolute constant $C$ such that, for every $\varepsilon \in (0, 1/10)$, every normalised instance $(n, k, d)$, every $\lambda \in [\varepsilon/k, 10k/\varepsilon]$ and $R$ with $\lambda < 6R$, and every client set $P''$ left by a terminated run of the preprocessing (input: $\lambda, R$ in real memory, $P''$ as a 0/1 array), with $N = \max(n, 2)$ and $T = N^{2^{C/\varepsilon}}$: on every random tape the run has halted after $\lfloor T\rfloor$ steps with work $\le T$, having output a list $S_{dp}$ of balls that covers $P''$ with radii in $[0, r_{\max}]$; and the event
--   $$\frac{\mathrm{cost}(S_{dp})}{1+\varepsilon} + \lambda|S_{dp}| \le \mathrm{cost}_\lambda(O_{3R})$$
--   (for every optimal $O_{3R}$) is measurable and has probability at least $1 - \varepsilon^2/n^4$.
--
--   Differences from the source:
--   - encoding: point set P with |P| = n, a metric d on P → points Fin n (0-based), d : Fin n → Fin n → ℝ with the published MinSumClust.IsMetric (d(p,p)=0, d ≥ 0, symmetry, triangle inequality, d(p,q) > 0 for p ≠ q); reason: same instances
--   - encoding: balls Ball(c, r) with r ∈ ℝ≥0 and sets of balls → Ball n = (center : Fin n, radius : ℝ) with point set {p : d(c,p) ≤ r}; arbitrary input/output balls carry 0 ≤ radius explicitly; mathematical sets of balls are Finsets; reason: same objects; a negative radius is not a ball (p. 1)
--   - encoding: a set S of balls output by an algorithm, |S|, cost(S) → a ball list read from the machine; |S| is its length and cost(S) the sum over its entries, a repeated ball counted every time; reason: an output without repetitions is a set; counting repetitions only makes the size and cost bounds harder to meet
--   - generalization: a (randomized, polynomial-time) algorithm on an unspecified machine → one MinSumFPT.Admissible program of the published randomized distance-oracle real RAM (unit cost per instruction; no floor, √, log/exp or pointer multiplication; rational literals); inputs in the documented extended layout initStateExt; reason: the machine has fewer primitives than any standard real RAM, so the statement implies the same statement on a richer machine
--   - reading: an algorithm that is given ε (or: "for any ε") → one program P and one constant C chosen before ε; ε is an input in mem 0; reason: "given any ε" makes ε an input of one algorithm, and the O(·) constants are absolute
--   - reading: time n^{2^{O(1/ε)}} → at most ⌊T⌋₊ steps and work ≤ T with T = N^(2^(C/ε)), N = max(n, 2), C absolute; reason: N = max(n, 2) makes the asymptotic bound an exact bound also at n = 1; increasing the absolute C absorbs fixed overhead for n ≥ 2. Asymptotic notation in the source does not impose a literal one-instruction bound at n = 1
--   - reading: running time of a randomized algorithm → worst case: on every tape ω the run has halted within the time bound with a well-formed output; reason: the paper's running times are deterministic bounds (pp. 23, 38–39); success, not time, is probabilistic
--   - reading: "outputs a set of balls that cover …, with radii ≤ … and [cost inequality] with probability at least …" → the covering, nonnegative-radius and radius-bound clauses hold on every tape; only the cost inequality is the probabilistic event; reason: the proof's cover and radius bounds hold for every random choice (Lemma 5.10, p. 20; proof of Lemma 6.7, p. 38); the stronger reading
--   - reading: the lemma's own sentence (context of §6) → explicit hypotheses: StandingInstance d k ε (Lemma 2.1's normalisation: integer distances in [1, ⌈10k/ε⌉], opt ≤ 8k/ε, 1 ≤ k ≤ n), ε ∈ (0, 1/10), λ ∈ [ε/k, 10k/ε] (Theorem 6.1); reason: p. 7 assumes the normalisation for the rest of the paper, p. 6 fixes ε ∈ (0, 1/10), and §6 works under Theorem 6.1's λ; trap 19 (section standing assumptions are binders)
--   - reading: P″ and O_{3R} of §6.2 (Case II, λ < 6R) → P″ := preFinal of any terminated run of the preprocessing (IsPreprocessingRun) from any client set P′, O_{3R} any optimal cover of P″ by balls of 𝔅 of radius ≤ 3R (IsOptCover); reason: the paper's preprocessing picks dense balls in an arbitrary order and O_{3R} is any optimal solution; the statement holds for all of them
--   - generalization: p. 26 assumes R ≤ ⌈10k/ε⌉ without loss before the bounded-radius DP analysis → no upper bound on R beyond the Case II condition λ < 6R; reason: this includes every source instance. Above the maximum distance all minimal balls are allowed and no dense preprocessing ball exists; extra threshold levels have empty nets and only a far child. The algorithm can cap R and use Case I if needed
-- source:
--   Fabrizio Grandoni, Anupam Gupta, Jatin Yadav, A PTAS for the Minimum Sum of Radii Problem, manuscript dated November 3, 2026 (STOC 2027 submission), SHA-256 99b43d49…, §6.2, Lemma 6.7, p. 27 (proof Appendix B, p. 38)

import Mathlib
import Definitions.Def_MinSumFPT_Machine
import Definitions.Def_MinSumRadiiPTAS_Main_Basic
import Definitions.Def_MinSumRadiiPTAS_Main_LP
import Definitions.Def_MinSumRadiiPTAS_Main_Partition
import Definitions.Def_MinSumRadiiPTAS_Main_CaseII
import Definitions.Def_MinSumRadiiPTAS_Main_Machine

open scoped Classical

namespace MinSumRadiiPTAS.Main

/-- **Lemma 6.7** (p. 27; proof p. 38): one admissible program `P` and one absolute constant `C` such
that, on every normalised instance with `ε ∈ (0, 1/10)`, every `λ ∈ [ε/k, 10k/ε]` and `R` with
`λ < 6R`, and every client set `P″` left by a terminated run of the preprocessing (input: `λ, R` in
real memory, `P″` as a 0/1 array), with `N = max(n, 2)` and `T = N^(2^(C/ε))`: on every tape the run
has halted after `⌊T⌋₊` steps with work `≤ T` and a ball list `S_dp` covering `P″` with radii in
`[0, r_max]`; and with probability at least `1 − ε²/n⁴`,
`cost(S_dp)/(1 + ε) + λ|S_dp| ≤ cost_λ(O_{3R})` for every optimal cover `O_{3R}` of `P″` by balls of
`𝔅` of radius `≤ 3R`. -/
theorem lemma_6_7 :
    ∃ P : MinSumFPT.Program, MinSumFPT.Admissible P ∧ ∃ C : ℕ,
      ∀ ε : ℝ, 0 < ε → ε < 1 / 10 →
      ∀ (n k : ℕ) (d : Fin n → Fin n → ℝ), StandingInstance d k ε →
      ∀ lam R : ℝ, ε / k ≤ lam → lam ≤ 10 * k / ε → lam < 6 * R →
      ∀ (P1 : Finset (Fin n)) (steps : List (Fin n × ℝ)),
        IsPreprocessingRun d lam ε R P1 steps →
        let P2 := preFinal d R P1 steps
        let N : ℕ := max n 2
        let T : ℝ := (N : ℝ) ^ ((2 : ℝ) ^ ((C : ℝ) / ε))
        let E : Set (ℕ → ℝ) := {ω | ∃ S : List (Ball n),
          OutputsBalls (runExt P n k ε [lam, R] P2 [] d ω ⌊T⌋₊) S ∧
            ∀ O : Finset (Ball n), IsOptCover d lam (fun B => B.radius ≤ 3 * R) P2 O →
              lcost S / (1 + ε) + lam * S.length ≤ costL lam O}
        (∀ ω : ℕ → ℝ, ∃ S : List (Ball n),
            OutputsBalls (runExt P n k ε [lam, R] P2 [] d ω ⌊T⌋₊) S ∧
              ((runExt P n k ε [lam, R] P2 [] d ω ⌊T⌋₊).work : ℝ) ≤ T ∧
              CoversL d S P2 ∧ ∀ B ∈ S, B.radius ≤ rmax ε R) ∧
          MeasurableSet E ∧
          ENNReal.ofReal (1 - ε ^ 2 / (n : ℝ) ^ 4) ≤ MinSumFPT.tapeLaw E := by sorry

end MinSumRadiiPTAS.Main
