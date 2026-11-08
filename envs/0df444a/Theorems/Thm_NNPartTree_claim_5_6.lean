-- Prove2me | Theorems.Thm_NNPartTree_claim_5_6
-- name    : NNPartTree.claim_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:11:52.181282+00:00
-- url     : https://prove2.me/theorems/776a5731-e4f1-4cd5-9ce5-038fb9860be2
-- title:
--   Claim 5.6, p.18 — a deterministic program outputs a feasible psd $M$ for $\Pi_{\mathrm{sdp}}(S,500c/\beta^2)$ with objective $O(1/\beta)(\mathrm{err}(f)+\varepsilon)$
-- statement:
--   There are a deterministic program, a constant $c>1$ and an exponent $K$ with the following. On input $d,k,\beta\in(0,1/2],\varepsilon\in(0,\beta/8)$ and a sample $S$ of $m$ pairs, the program halts within $c((d+k)^km(1+\log(1/\varepsilon)))^K$ work, on every $S$. If $f$ is a cut with $\mathrm{bal}_{\mathcal D}(f)\ge\beta$, approximated to $\varepsilon$ in degree $k$, and $m\ge 4000c/\beta^2$, then with probability at least $0.9$ over $S\sim\mathcal D^m$ the output matrix $M$ is feasible for $\Pi_{\mathrm{sdp}}(S,500c/\beta^2)$ and
--   $$\frac1m\sum_{i=1}^mV_i^\top MV_i\le\frac c\beta\big(\mathrm{err}_{\mathcal D}(f)+\varepsilon\big).$$
--
--   This is the algorithmic core of the improper learner.
--
--   Differences from the source:
--   - reading: no machine is named → the sampling real RAM `NNPartTree.Machine`; reason: the paper leaves the model open
--   - reading: outputs a psd matrix feasible for Π_sdp, and with probability 0.9 the objective bound holds → halting on every S; feasibility and objective bound together on the probability-0.9 event; reason: on a sample whose y-values coincide (i) and (ii) are inconsistent, so feasibility cannot hold on every S; exact feasibility is what Claim 5.7 uses
--   - reading: probability at least 0.9 over S → a program with neither coins nor samples; reason: the printed probability is over S alone
--   - generalization: bound with OPT_β(F) for F with approximation degree k(·) → each f with bal(f) ≥ β approximated at ε, with k an input; reason: the program does not depend on f, and an optimal f gives the printed form
--   - encoding: S ∼ D^m, matrix in ℝ^{N×N} → input layout `sampleInput`, output in the order of `monomials d k`, d ≥ 1, m ≥ 1; reason: the page fixes no layout or order; ℝ⁰ and an empty sample carry nothing
-- source:
--   Khanna, Padaki, Waingarten, Learning Partition Trees for Nearest Neighbor Search, arXiv:2607.09909 (held copy of 2026-11-03, sha256 d32992f2…), Claim 5.6, p.18; proof pp.18–19; Definition 5.5, p.18

import Mathlib
import Definitions.Def_NNPartTree_Learner

open MeasureTheory

namespace NNPartTree

/-- **Claim 5.6**, p.18; proof pp.18–19. S. Khanna, A. Padaki, E. Waingarten, *Learning Partition Trees for Nearest Neighbor Search*, arXiv:2607.09909 (held copy of 2026-11-03, sha256 d32992f2…).

There is a program, deterministic and taking the sample as input, that on every sample `S` halts within
`c ((d + k)^k m (1 + log(1/ε)))^K` work, and such that for every `f` as in Lemma 5.4, when `m ≥ 4000 c/β²`, with
probability at least `0.9` over `S ∼ D^m` its output is a psd matrix feasible for `Π_sdp(S, 500 c/β²)` with
objective at most `(c/β)(err_D(f) + ε)`.

**Formalization Note.** The program is on the machine `NNPartTree.Machine`, and the output matrix is in the
order of `monomials d k`. Halting holds on every `S`, and feasibility with the objective bound on the event of
probability `0.9`: on a sample whose `y`s coincide, (i) and (ii) are inconsistent, so no feasible matrix exists.
The program takes `k` as input and does not depend on `f`. Stating each `f` implies the form with `OPT_β(F)`. -/
theorem claim_5_6 : ∃ Solver : Program, DetProgram Solver ∧ ∃ c : ℝ, 1 < c ∧ ∃ K : ℕ,
    ∀ (d k m : ℕ) (β ε : ℝ), 1 ≤ d → 1 ≤ m → 0 < β → β ≤ 1 / 2 → 0 < ε → ε < β / 8 →
      (∀ S : Fin m → Pt d × Pt d, ∃ st, IsFinal Solver 0 (sampleInput k S β ε) (noCoins, noStream) st ∧
        (st.work : ℝ) ≤ c * (((d : ℝ) + k) ^ k * m * (1 + Real.log (1 / ε))) ^ K) ∧
      ∀ (D : Measure (Pt d × Pt d)) [IsProbabilityMeasure D] (f : Pt d → ℝ), IsCut f →
        β ≤ bal D f → ApproxAt D f ε k → 4000 * c / β ^ 2 ≤ m →
        sampleProduct D m {S | ¬ ∃ st,
            IsFinal Solver 0 (sampleInput k S β ε) (noCoins, noStream) st ∧
            SdpFeasible (k := k) S (500 * c / β ^ 2) (outputMatrix (numMonomials d k) st) ∧
            sdpObjective (k := k) S (outputMatrix (numMonomials d k) st) ≤ c / β * (err D f + ε)} ≤
          ENNReal.ofReal (1 / 10) := by sorry

end NNPartTree
