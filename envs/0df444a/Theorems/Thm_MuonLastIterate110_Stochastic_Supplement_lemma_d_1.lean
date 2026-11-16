-- Prove2me | Theorems.Thm_MuonLastIterate110_Stochastic_Supplement_lemma_d_1
-- name    : MuonLastIterate110.Stochastic.Supplement.lemma_d_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T04:40:29.632447+00:00
-- url     : https://prove2.me/theorems/fa680140-9685-4267-acb6-95e5f19b6873
-- title:
--   Lemma D.1 — summability implies a density-one rate
-- statement:
--   Let $a_t\ge0$ for every integer $t\ge1$, let $0\le p<1$, and let $s>0$ be a real number. If
--
--   $$
--   \sum_{t=1}^\infty t^{-p}a_t^s<\infty,
--   $$
--
--   then
--
--   $$
--   a_t=o_{\mathrm{dens}}\bigl(t^{-(1-p)/s}\bigr).
--   $$
--
--   Here $o_{\mathrm{dens}}$ has the exact exceedance-density meaning of Definition 6.2, for every positive threshold multiple. This general sequence result supplies the rate conversion for all cases of Theorem 6.3, while allowing any positive real $s$.
--
--   **Formalization Note** The hypothesis is real `Summable` of the nonnegative sequence $t^{-p}a_t^s$, shifted to start at one; all powers with real exponent use real powers.
--
--   Differences from the source:
--
--   - encoding: the series Σ t^{-p} a_t^s from t = 1 and the notation o_dens → Summable of the sequence at t + 1, Real.rpow, and DensityOne; reason: nonnegativity gives equivalence with finite total sum; s is any positive real and the density predicate is Definition 6.2
-- source:
--   Ping Li and Vincent Y. F. Tan, Last-Iterate Stationarity of Muon with Finitely Many Newton-Schulz Iterations, STOC 2027 submission #110 preprint (2026), source.pdf SHA-256 5362e7185a9ddcba39d1a70da110a8b04f1d179ad818e6d5d0ec73bf29586372, p.28, Lemma D.1. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/110.pdf

import Mathlib
import Definitions.Def_MuonLastIterate110_Stochastic_Supplement_DensityOne

open Filter Topology

namespace MuonLastIterate110.Stochastic.Supplement

/-- Lemma D.1, p.28: arbitrary real exponent s > 0, with all sums starting at t = 1. -/
theorem lemma_d_1 (a : ℕ → ℝ) (p s : ℝ)
    (ha : ∀ t : ℕ, 1 ≤ t → 0 ≤ a t) (hp : 0 ≤ p) (hp' : p < 1) (hs : 0 < s)
    (hsum : Summable (fun t : ℕ => ((t + 1 : ℕ) : ℝ) ^ (-p) * a (t + 1) ^ s)) :
    DensityOne a (fun t => (t : ℝ) ^ (-(1 - p) / s)) := by sorry

end MuonLastIterate110.Stochastic.Supplement
