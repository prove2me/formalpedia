-- Prove2me | Theorems.Thm_GaussMixHH_Supplement_theorem_4
-- name    : GaussMixHH.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:38:11.812244+00:00
-- url     : https://prove2.me/theorems/31507fa1-d010-4ecb-b590-ba05753b755a
-- title:
--   Theorem 4, p.5 — recovering every heavy center with $n^{O(k)}+\exp(\exp(O(k)))+\exp(O(k^{2/3}n^{1/3}))$ samples, $k=\log^2(1/\varepsilon_{wt})/\varepsilon_{dist}^2$
-- statement:
--   **Homogeneous mixture — recovery algorithm.** Let $0<\varepsilon_{wt}\le1/8$ and $0<\varepsilon_{dist}<\Delta_{\min}/2$, where $\Delta_{\min}$ is at most an absolute constant. For $n$ sufficiently large in terms of $\varepsilon_{wt}$ and $\varepsilon_{dist}$, there is an algorithm $\mathrm{Recover}(\varepsilon_{wt},\varepsilon_{dist},\Delta_{\min})$ that solves the recovery problem (RP) for mixtures of identity-covariance Gaussians over $\mathbb R^n$ with probability at least $9/10$. With
--
--   $$k:=\frac{\log^2(1/\varepsilon_{wt})}{\varepsilon_{dist}^2},$$
--
--   its sample complexity is at most
--
--   $$n^{O(k)}+\exp(\exp(O(k)))+\exp(O(k^{2/3}n^{1/3})),$$
--
--   and its running time is at most
--
--   $$n^{O(k)}+\exp(\exp(\widetilde O(k)))+\exp(O(k^{2/3}n^{1/3})).$$
--
--   (RP) asks, from i.i.d. samples of $\mathrm{Mix}(\mathcal D,1)$ for a probability distribution $\mathcal D$ on $\Delta_{\min}$-separated centers, for a list $(z_j,\widehat w_j)_{j\le L}$ and an injective map $\rho$ from the list into the centers such that every $z_j$ is within $\varepsilon_{dist}$ of $\rho(j)$ with $|\widehat w_j-\mathcal D(\rho(j))|\le\varepsilon_{wt}$, and every center of weight at least $2\varepsilon_{wt}$ is some $\rho(j)$.
--
--   This is the paper's answer to the heavy-hitter question for Gaussian mixtures: all heavy components are found, with their weights, using a number of samples independent of the number of components and subexponential in $n$.
--
--   **Formalization Note** The machine is the mission's published real RAM (`GaussMixHH.Machine`), as for Theorem 1: one admissible program serves all inputs, receives $n,\varepsilon_{wt},\varepsilon_{dist},\Delta_{\min}$, sees $\mathcal D$ only through `sample`, and returns the list in the layout of `RecoveryLayout`; the list length is unbounded. "At most an absolute constant" is $\Delta_{\min}\le\Delta_0$ for some $\Delta_0>0$; every $O(\cdot)$ is one constant $C>0$; $\widetilde O(k)$ is $C\,k\,(1+\log(1+k))^{C}$; "$n$ sufficiently large" is $n\ge n_0(\varepsilon_{wt},\varepsilon_{dist})$. The program, $\Delta_0$, $C$ and $n_0$ are chosen before all parameters. Both cost bounds hold on every coin tape and sample stream (the run halts within them), and (RP) holds on a measurable event of probability $\ge9/10$ of the coin-and-sample space, for every probability measure $\mathcal D$ with $\Delta_{\min}$-separated atoms (possibly infinitely many).
--
--   Differences from the source:
--   - reading: there is an algorithm Recover(εwt, εdist, ∆min); running time → ∃ an Admissible program P of the published GaussMixHH.Machine with input recoverInput n εwt εdist Δmin; running time = work, sample complexity = samplesUsed, both bounded on every coin tape and sample stream; reason: §3, p.15: running times are in the real arithmetic model; the same reading as the published Theorem 1
--   - reading: output list z1, …, zL, ŵ1, …, ŵL → outLength / outPoint / outWeight of the RecoveryLayout definition (L in pointer 1, blocks of n + 1 memory cells); reason: the paper names no output layout; L is unrestricted
--   - reading: injective map ρ from z1, …, zL to Supp → ρ : Fin L → ℝⁿ injective with values in Supp D; reason: indexing by list positions; it implies the paper's map on points and coincides with it for lists without repeated points, which (RP) forces when εdist < ∆min/2
--   - encoding: ∆min is at most an absolute constant; O(·), Õ(k); n sufficiently large in terms of εwt and εdist → ∃ Δ₀ > 0 with Δmin ≤ Δ₀; one constant C > 0 in every O; Õ(k) = C·k·(1 + log(1 + k))^C; n ≥ n₀ εwt εdist; P, Δ₀, C, n₀ chosen before all parameters; reason: Lean rendering of the asymptotic notation; n₀ does not depend on ∆min, as printed
--   - reading: solves (RP) with probability at least 9/10 → a measurable event E with sampleSpace D E ≥ 9/10 on which every halted state's output satisfies (RP), for every probability measure D with IsSeparatedAtomic Δmin D (Supp possibly infinite); reason: the probability space is fair coins × i.i.d. samples of Mix(D, 1), as in the published Theorem 1; the model of p.2 allows infinite Supp
-- source:
--   De, Huang, Nadimpalli, Servedio, Optimally learning mixtures of arbitrarily many Gaussians, STOC 2027 submission (manuscript sha256 4f36a53e…), Theorem 4, p.5 (PDF p.7), restated p.39 (PDF p.41); (RP) p.3; proof §7, pp.40–43

import Mathlib
import Definitions.Def_GaussMixHH_Machine
import Definitions.Def_GaussMixHH_CenterModel
import Definitions.Def_GaussMixHH_Supplement_RecoveryLayout

open MeasureTheory ProbabilityTheory

namespace GaussMixHH.Supplement

open GaussMixHH

/-- **Theorem 4** (Homogeneous mixture — recovery algorithm).

A. De, Y. Huang, S. Nadimpalli, R. A. Servedio, *Optimally learning mixtures of arbitrarily many
Gaussians*, STOC 2027 submission (manuscript sha256 4f36a53e…), Theorem 4, p.5 (PDF p.7), restated
p.39 (PDF p.41); (RP) on p.3.

"Let 0 < εwt ≤ 1/8 and 0 < εdist < ∆min/2, where ∆min is at most an absolute constant. For n
sufficiently large in terms of εwt and εdist, there is an algorithm Recover(εwt, εdist, ∆min) that
solves (RP) for mixtures of identity covariance Gaussians over Rⁿ with probability at least 9/10.
Set k := log²(1/εwt)/ε²dist. Its sample complexity is at most
n^{O(k)} + exp(exp(O(k))) + exp(O(k^{2/3}n^{1/3})), and its running time is at most
n^{O(k)} + exp(exp(Õ(k))) + exp(O(k^{2/3}n^{1/3}))."

**Formalization Note.**
* The machine is the published `GaussMixHH.Machine` (the real arithmetic model, p.15), as in
  Theorem 1. One `Admissible` program `P` serves every input; it receives `n` and
  `εwt, εdist, ∆min` (`recoverInput`) and sees `D` only through `sample`. The output list is read
  at `halt` with the layout of `RecoveryLayout` (length in pointer `1`, then `(z_j, ŵ_j)` blocks of
  `n + 1` memory cells); the length is unbounded.
* "∆min is at most an absolute constant": `∃ Δ₀ > 0` with `∆min ≤ Δ₀`. Every `O(·)` is one constant
  `C > 0`; `Õ(k)` is `C·k·(1 + log(1 + k))^C` (polylogarithmic factors with their power folded into
  `C`). "n sufficiently large in terms of εwt and εdist": `n₀(εwt, εdist)`, not depending on `∆min`.
  `P, Δ₀, C, n₀` are chosen before all parameters. `log` is `Real.log`; `k = log(1/εwt)²/εdist²`
  (log squared).
* The sample bound `n^{Ck} + exp(exp(Ck)) + exp(C k^{2/3} n^{1/3})` and the work bound
  `n^{Ck} + exp(exp(C k (1 + log(1 + k))^C)) + exp(C k^{2/3} n^{1/3})` hold on every coin tape and
  sample stream (the run halts within them).
* Randomness: `sampleSpace D` = fair coin tape × i.i.d. samples of `Mix(D, 1)`. (RP) holds on a
  measurable set of probability `≥ 9/10` for every probability measure `D` that is purely atomic
  with `∆min`-separated atoms (`IsSeparatedAtomic`, `Supp D` possibly infinite). -/
theorem theorem_4 :
    ∃ (P : Program) (_ : Admissible P) (Δ₀ C : ℝ) (n₀ : ℝ → ℝ → ℕ), 0 < Δ₀ ∧ 0 < C ∧
      ∀ (εwt εdist Δmin : ℝ), 0 < εwt → εwt ≤ 1 / 8 → 0 < εdist → 2 * εdist < Δmin →
      Δmin ≤ Δ₀ →
      ∀ n : ℕ, n₀ εwt εdist ≤ n →
      ∀ (D : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure D],
        IsSeparatedAtomic Δmin D →
        let k := Real.log (1 / εwt) ^ 2 / εdist ^ 2
        let third := C * k ^ ((2 : ℝ) / 3) * (n : ℝ) ^ ((1 : ℝ) / 3)
        let S := (n : ℝ) ^ (C * k) + Real.exp (Real.exp (C * k)) + Real.exp third
        let W := (n : ℝ) ^ (C * k) +
          Real.exp (Real.exp (C * k * (1 + Real.log (1 + k)) ^ C)) + Real.exp third
        (∀ ω, ∃ t, (run P n (recoverInput n εwt εdist Δmin) ω t).halted = true ∧
          ((run P n (recoverInput n εwt εdist Δmin) ω t).work : ℝ) ≤ W ∧
          ((run P n (recoverInput n εwt εdist Δmin) ω t).samplesUsed : ℝ) ≤ S) ∧
        ∃ E, MeasurableSet E ∧ 9 / 10 ≤ (sampleSpace D E).toReal ∧
          ∀ ω ∈ E, ∀ t, (run P n (recoverInput n εwt εdist Δmin) ω t).halted = true →
            IsRecoveryOutput D εwt εdist (outLength (run P n (recoverInput n εwt εdist Δmin) ω t))
              (outPoint n (run P n (recoverInput n εwt εdist Δmin) ω t))
              (outWeight n (run P n (recoverInput n εwt εdist Δmin) ω t)) := by sorry

end GaussMixHH.Supplement
