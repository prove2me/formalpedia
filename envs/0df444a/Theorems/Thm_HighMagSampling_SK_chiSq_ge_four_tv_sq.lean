-- Prove2me | Theorems.Thm_HighMagSampling_SK_chiSq_ge_four_tv_sq
-- name    : HighMagSampling.SK.chiSq_ge_four_tv_sq
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:27:02.807604+00:00
-- url     : https://prove2.me/theorems/57d847cc-284e-4ac6-a80d-55a72e00ee93
-- title:
--   §2.2 — comparison inequality $\chi^2(\mu\|\pi)\ge 4\,\mathrm{TV}(\mu,\pi)^2$
-- statement:
--   Let $\mu,\pi$ be probability measures on a measurable space $\Omega$. The total variation distance is $\mathrm{TV}(\mu,\pi)=\sup_E\,\mu(E)-\pi(E)$ over measurable $E$, and the $\chi^2$-divergence is $\chi^2(\mu\|\pi)=\int(\tfrac{d\mu}{d\pi}-1)^2\,d\pi$ when $\mu\ll\pi$ and $+\infty$ otherwise. Then
--   $$\chi^2(\mu\|\pi)\ \ge\ 4\,\mathrm{TV}(\mu,\pi)^2 .$$
--
--   Together with Lemma 1 this converts the $\chi^2$ contraction of the lazy down-up walk into the total-variation guarantee of Theorem 4.
--
--   **Formalization Note.** TV and $\chi^2$ are the published `PolySampIso.tvDist` and `PolySampIso.chiSq`; $\chi^2$ is $[0,\infty]$-valued, and the inequality is stated in $[0,\infty]$.
--
--   Differences from the source:
--   - reading: densities $\mu(\omega)/\nu(\omega)$ on a general $\Omega$ → the Radon–Nikodym derivative $d\mu/d\nu$, and $\chi^2=+\infty$ when $\mu\not\ll\nu$; reason: §2.1 writes the formulas with "$d\omega$ a counting measure if $\Omega$ is discrete"; this is their measure-theoretic meaning.
--   - encoding: $\mathrm{TV}(\mu,\nu)=\sup_E\mu(E)-\nu(E)$ → $\sup_B|\mu(B)-\nu(B)|$ (`PolySampIso.tvDist`); reason: equal for probability measures (pass to the complement).
--   - encoding: $\chi^2\ge4\mathrm{TV}^2$ in $\mathbb R$ → `ENNReal.ofReal (4 * TV²) ≤ χ²` in $[0,\infty]$; reason: $\chi^2$ may be $+\infty$; same instances.
-- source:
--   Kumar, Sarkar, Tian, Zhu, High-Magnetization Sampling at Low Temperatures, arXiv:2609.08873v1, p. 11, §2.2, comparison inequality; p. 9, §2.1 (TV, χ²)

import Mathlib
import Definitions.Def_PolySampIso_Divergences

open MeasureTheory
open scoped ENNReal

namespace HighMagSampling.SK

/-- §2.2, p. 11, the comparison inequality: `χ²(μ ‖ π) ≥ 4 TV(μ, π)²` for probability measures on
a general measurable space. -/
theorem chiSq_ge_four_tv_sq {Ω : Type*} [MeasurableSpace Ω] (μ π : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure π] :
    ENNReal.ofReal (4 * PolySampIso.tvDist μ π ^ 2) ≤ PolySampIso.chiSq μ π := by sorry

end HighMagSampling.SK
