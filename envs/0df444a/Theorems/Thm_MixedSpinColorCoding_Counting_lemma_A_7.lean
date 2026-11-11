-- Prove2me | Theorems.Thm_MixedSpinColorCoding_Counting_lemma_A_7
-- name    : MixedSpinColorCoding.Counting.lemma_A_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:03:46.05638+00:00
-- url     : https://prove2.me/theorems/0e6bde7a-b6ad-44c6-9394-1a8d7908d564
-- title:
--   Lemma A.7 — uniform lower bound for the normalized partition function on the complex disk
-- statement:
--   Fix a nonzero mixture with $p_{\max}\ge2$ and $0<\beta_*<\beta_{2\mathrm{nd}}$ (the standing assumptions of Appendix A). There are constants $c>0$, $C\ge1$ and a sequence $\zeta_n\to0$, depending only on the mixture and $\beta_*$, such that for every $n\ge1$ and every $0<\alpha<1/2$,
--   $$\mathbb P_G\Big[\inf_{z\in\mathbb C,\ |z|\le\beta_*}|Y_G(z)|\ge C^{-1}\alpha^c\Big]\ge1-\zeta_n-\alpha .$$
--
--   Differences from the source:
--   - encoding: $\mathbb P_G[\inf_{|z|\le\beta_*}|Y_G(z)|\ge C^{-1}\alpha^c]\ge1-\zeta_n-\alpha$ → a measurable set of disorders of probability at least $1-\zeta_n-\alpha$ on which $|Y_G(z)|\ge C^{-1}\alpha^c$ for every $|z|\le\beta_*$; reason: the infimum over the compact disk of a continuous function is attained, so the bound on the infimum is the bound at every point; a measurable subset avoids Lean's outer measure on an event whose measurability is not given, and implies the source's probability bound
--   - encoding: $\zeta_n=o(1)$, sites $[n]$, the implicit dimension $n$ → `Tendsto ζ atTop (𝓝 0)`, `Fin n`, $n\ge1$; reason: Lean conventions; the source's normalization $n^{-(p-1)/2}$ needs $n\ge1$
-- source:
--   Alina Harbuzova, Saba Lepsveridze, Mahbod Majid, Ankur Moitra, STOC 2027 submission #592 (October 2026), Color Coding for the Sherrington–Kirkpatrick Model, Lemma A.7, printed p.28 / PDF p.30; standing assumptions §A.1–A.2, PDF pp.22–23. PDF SHA-256 5559e422541f71e2e270b74941f426295f0ea249bd88d4ff218bb950ad81646b; citation_basis: published.

import Mathlib
import Definitions.Def_MixedSpinColorCoding_Counting_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal

namespace MixedSpinColorCoding.Counting

/-- Lemma A.7, STOC 2027 submission #592, PDF p.30, under the standing assumptions of
Appendix A (a fixed nonzero mixture with `pmax ≥ 2` and `0 < β_* < β_2nd`). There are
constants `c > 0`, `C ≥ 1` and a sequence `ζ_n → 0` such that for every `n ≥ 1` and every
`0 < α < 1/2`, with probability at least `1 − ζ_n − α` (inner measure: a measurable set of that
probability), `|Y_G(z)| ≥ C⁻¹ α^c` for every complex `z` with `|z| ≤ β_*`. -/
theorem lemma_A_7 (pmax : ℕ) (hpmax : 2 ≤ pmax) (γ : ℕ → ℝ) (hγ : NonzeroMixture pmax γ)
    (βstar : ℝ) (hβ0 : 0 < βstar) (hβ : βstar < beta2nd pmax γ) :
    ∃ (c C : ℝ) (ζ : ℕ → ℝ), 0 < c ∧ 1 ≤ C ∧ Tendsto ζ atTop (𝓝 0) ∧
      ∀ n : ℕ, 1 ≤ n → ∀ α : ℝ, 0 < α → α < 1 / 2 →
        ∃ S : Set (Disorder n pmax), MeasurableSet S ∧
          (∀ G ∈ S, ∀ z : ℂ, ‖z‖ ≤ βstar →
            C⁻¹ * α ^ c ≤ ‖normalizedPartitionFunction n pmax γ G z‖) ∧
          ENNReal.ofReal (1 - ζ n - α) ≤ disorderLaw n pmax S := by sorry

end MixedSpinColorCoding.Counting
