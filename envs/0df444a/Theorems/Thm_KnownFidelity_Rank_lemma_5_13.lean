-- Prove2me | Theorems.Thm_KnownFidelity_Rank_lemma_5_13
-- name    : KnownFidelity.Rank.lemma_5_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:48:07.671578+00:00
-- url     : https://prove2.me/theorems/ee744abe-1424-4f66-8ea8-cd9006766724
-- title:
--   Lemma 5.13 — Ginibre nuclear norm $\mathbb P[\|Z_s\|_1\le c_gs^{3/2}]\le e^{-c'_gs^2}$
-- statement:
--   There are universal constants $c_g,c_g'>0$ such that, for every $s\ge1$ and every standard complex Ginibre matrix $Z_s\in\mathbb C^{s\times s}$ (independent entries with density $\pi^{-1}e^{-|z|^2}$),
--
--   $$\mathbb P\big[\|Z_s\|_1\le c_g\,s^{3/2}\big]\ \le\ e^{-c_g' s^2}.$$
--
--   It shows that the spread-out prior has large $T_j$ with overwhelming probability.
--
--   Differences from the source:
--   - encoding: a standard complex Ginibre matrix Z_s → Z_s ∼ ginibreLaw s (product of the platform's complexGaussian over the s² entries); reason: the law of independent entries with real and imaginary parts N(0, 1/2), i.e. density π^{−1}e^{−|z|²}
-- source:
--   Lee, Jo, Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank, arXiv:2608.01770, Lemma 5.13, p. 22 (PDF p. 24)

import Mathlib
import Definitions.Def_KnownFidelity_Rank_ginibreLaw
import Definitions.Def_WildeQIT_traceNorm

open MeasureTheory

namespace KnownFidelity.Rank

/-- **Lemma 5.13 (Ginibre nuclear norm).**
Lee, Jo, *Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank*,
arXiv:2608.01770, Lemma 5.13, printed p. 22 (PDF p. 24): "There are universal constants c_g, c′_g > 0 such
that, for every s ≥ 1 and every standard complex Ginibre matrix Z_s ∈ C^{s×s},
P[∥Z_s∥₁ ≤ c_g s^{3/2}] ≤ e^{−c′_g s²}. (69)"

**Formalization Note.** `Z_s ∼ ginibreLaw s`: independent entries with density `π^{−1}e^{−|z|²}` (§5.4, printed p. 17).
`∥·∥₁` is `WildeQIT.traceNorm`. The constants come before `s`. -/
theorem lemma_5_13 :
    ∃ cg cg' : ℝ, 0 < cg ∧ 0 < cg' ∧ ∀ s : ℕ, 1 ≤ s →
      ginibreLaw s
          {Z | WildeQIT.traceNorm Z ≤ cg * (s : ℝ) ^ ((3 : ℝ) / 2)} ≤
        ENNReal.ofReal (Real.exp (-cg' * (s : ℝ) ^ 2)) := by sorry

end KnownFidelity.Rank
