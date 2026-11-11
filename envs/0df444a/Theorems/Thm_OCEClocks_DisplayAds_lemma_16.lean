-- Prove2me | Theorems.Thm_OCEClocks_DisplayAds_lemma_16
-- name    : OCEClocks.DisplayAds.lemma_16
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:23:17.200947+00:00
-- url     : https://prove2.me/theorems/1aa23fa2-b15b-409a-af53-8f82ffc36893
-- title:
--   Lemma 16 — tail bounds for reachable measures
-- statement:
--   Let $\lambda>0$ and let $\nu$ be a reachable measure: obtained from $\pi=\mathrm{Exp}(\lambda)$ by a finite sequence of matching kernels $M_x$ ($x\in[0,1]$) and gap kernels $G_t$ ($t\ge0$). Then $a\mapsto e^{\lambda a}\,\nu([a,\infty))$ is nondecreasing on $a\ge0$ and at most one. In particular, for $a\ge0$,
--
--   $$(\nu\mathbf 1)\,e^{-\lambda a}\ \le\ \nu([a,\infty))\ \le\ e^{-\lambda a}.$$
--
--   Conditioning on losing every comparison favours older ages. These tail bounds reduce the inequalities of Lemmas 18 and 19 to checks against $\pi$.
--
--   **Formalization Note** All quantities are in $[0,\infty]$ (`ℝ≥0∞`), so no finiteness of $\nu$ is assumed. $\nu\mathbf 1=\nu(\mathbb R)$ is the total mass; reachable measures live on $[0,\infty)$.
--
--   Differences from the source:
--   - generalization: λ = 4.5 ("The rest of the paper fixes λ = 4.5", p. 9) → every λ > 0; reason: the printed statement does not depend on the value of λ; at λ = 9/2 the Lean statement is the paper's
--   - encoding: expectations conditional on A(0) = a → the age process started at age a (last arrival at time −a, later arrivals at partial sums of i.i.d. Exp(λ) gaps, one independent Unif[0,1] for the request's clock); reason: this is how the paper evaluates these conditional expectations (proofs of Lemmas 16 and 32); by memorylessness it is the conditional law given A(0) = a
--   - encoding: measures and functions on ages [0, ∞) → finite measures on ℝ and functions ℝ → ℝ; only ages a ≥ 0 occur, and boundedness/regularity hypotheses are imposed on [0, ∞) only; reason: Lean convention; same instances
-- source:
--   Huang, Patton, Yang, Zhao, Online Correlated Exponential Clocks, STOC 2027 submission (manuscript of November 3, 2026, sha256 820333a3…), p. 15, Lemma 16 (proof p. 40, B.4)

import Mathlib
import Definitions.Def_OCEClocks_DisplayAds_Kernels

open MeasureTheory

namespace OCEClocks.DisplayAds

/-- Lemma 16 (p. 15): for every reachable measure `ν`, `e^{λa} ν([a, ∞))` is nondecreasing in
`a ≥ 0` and at most one; in particular `(ν1) e^{-λa} ≤ ν([a, ∞)) ≤ e^{-λa}` for `a ≥ 0`. -/
theorem lemma_16 (lam : ℝ) (hlam : 0 < lam) (ν : Measure ℝ) (hν : Reachable lam ν) :
    MonotoneOn (fun a => ENNReal.ofReal (Real.exp (lam * a)) * ν (Set.Ici a)) (Set.Ici 0) ∧
    (∀ a : ℝ, 0 ≤ a → ENNReal.ofReal (Real.exp (lam * a)) * ν (Set.Ici a) ≤ 1) ∧
    (∀ a : ℝ, 0 ≤ a →
      ν Set.univ * ENNReal.ofReal (Real.exp (-(lam * a))) ≤ ν (Set.Ici a) ∧
        ν (Set.Ici a) ≤ ENNReal.ofReal (Real.exp (-(lam * a)))) := by sorry

end OCEClocks.DisplayAds
