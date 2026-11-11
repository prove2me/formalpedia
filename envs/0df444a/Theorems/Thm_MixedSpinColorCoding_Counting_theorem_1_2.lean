-- Prove2me | Theorems.Thm_MixedSpinColorCoding_Counting_theorem_1_2
-- name    : MixedSpinColorCoding.Counting.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:05:42.779993+00:00
-- url     : https://prove2.me/theorems/4c2bd670-2611-4242-91f2-8fa9fda907b7
-- title:
--   Theorem 1.2 — deterministic polynomial-time approximation of mixed p-spin partition functions (corrected: additive constant overhead in the operation bound)
-- statement:
--   Fix a nonzero mixture $\xi(q)=\sum_{p=2}^{p_{\max}}\gamma_p^2q^p$ with $p_{\max}\ge2$, and $0<\beta_*<\beta_{2\mathrm{nd}}$. There exist one admissible deterministic program $P$ of the exact-arithmetic machine, a constant $C$ and a sequence $\zeta_n\to0$ such that for every $n\ge1$ and all $\varepsilon,\delta>0$: on every disorder $G$ and every real $\beta$ with $|\beta|\le\beta_*$, the run of $P$ on $(n,\gamma,G,\varepsilon,\delta,\beta)$ halts within $C+(n/(\varepsilon\delta))^C$ unit-cost steps, all preprocessing included; and, writing $\widehat Z_G(\beta)$ for its output,
--   $$\mathbb P_G\Big[\sup_{|\beta|\le\beta_*}\Big|\frac{\widehat Z_G(\beta)}{Z_G(\beta)}-1\Big|\le\varepsilon\Big]\ge1-\zeta_n-\delta .$$
--
--   Differences from the source:
--   - correction: at most $(n/(\varepsilon\delta))^C$ operations for all $\varepsilon,\delta>0$ → at most $C+(n/(\varepsilon\delta))^C$ steps; reason: the printed bound is below $1$ whenever $\varepsilon\delta>n$ (e.g. SK, $p_{\max}=2$, $\gamma_2=1/\sqrt2$, $\beta_*=1/2<\beta_{2\mathrm{nd}}=1$, $n=2$, $\varepsilon=\delta=2$: $2^{-C}<1$), so on those inputs the algorithm would have to answer with zero operations, while for the same $n$ and small $\varepsilon,\delta$ it must compute; a fixed program cannot tell the two cases apart without a unit-cost comparison. The additive constant is exactly that overhead: for $\varepsilon,\delta<1$ and $n\ge2$ one has $n/(\varepsilon\delta)\ge2$ and $C+x^C\le x^{C'}$ for a larger $C'$, and the proof's own bound $(n/(\varepsilon\delta))^{O(1)}$ is unchanged there
--   - reading: "the exact-arithmetic model" with unit-cost arithmetic, comparisons and elementary functions → the published real pointer machine extended by pointer-to-real cast, $\sqrt{\cdot},\exp,\log$ and halt, rational literals, the coefficients $\gamma_p$ supplied as input cells; reason: the source names no instruction set; every instruction here is a unit-cost operation of footnote 2, so a program here is an algorithm of the source, and the fixed coefficients are read from memory instead of being program literals
--   - reading: "evaluating $\widehat Z_G(\beta)$ requires at most … operations" → the whole run on $(n,\gamma,G,\varepsilon,\delta,\beta)$, preprocessing and circuit construction included, halts within the bound on every disorder and every $|\beta|\le\beta_*$; reason: the proof charges construction and evaluation together (PDF p.31); charging everything per run only strengthens the bound
--   - encoding: $\mathbb P_G[\sup_{|\beta|\le\beta_*}|\widehat Z_G/Z_G-1|\le\varepsilon]\ge1-\zeta_n-\delta$ → a measurable set of disorders of probability at least $1-\zeta_n-\delta$ on which $|\widehat Z_G(\beta)/Z_G(\beta)-1|\le\varepsilon$ for every $|\beta|\le\beta_*$; reason: the supremum bound is the pointwise bound for all $\beta$ in the interval; a measurable subset avoids Lean's outer measure on an event whose measurability is not given, and implies the source's probability bound
--   - encoding: $\zeta_n=o(1)$, the constant $C$, sites $[n]$, the implicit dimension $n$ → `Tendsto ζ atTop (𝓝 0)`, `C : ℕ`, `Fin n`, $n\ge1$ given to the program as pointer $p[0]$; reason: Lean conventions; a real exponent can be rounded up to a natural one since the base is used only through the bound $C+x^C$ with $x\ge0$ and the source's $C$ is existential
-- source:
--   Alina Harbuzova, Saba Lepsveridze, Mahbod Majid, Ankur Moitra, STOC 2027 submission #592 (October 2026), Color Coding for the Sherrington–Kirkpatrick Model, Theorem 1.2 and footnote 2, printed p.2 / PDF p.4; proof printed p.29 / PDF p.31. PDF SHA-256 5559e422541f71e2e270b74941f426295f0ea249bd88d4ff218bb950ad81646b; citation_basis: published.

import Mathlib
import Definitions.Def_MixedSpinColorCoding_Counting_Model
import Definitions.Def_MixedSpinColorCoding_Counting_Machine

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal

namespace MixedSpinColorCoding.Counting

/-- Theorem 1.2 (corrected: additive constant overhead in the operation bound), STOC 2027
submission #592, PDF p.4. Fix `pmax ≥ 2`, a nonzero mixture `γ` and `0 < β_* < β_2nd`. There
are one admissible deterministic program `P`, a constant `C` and a sequence `ζ_n → 0` such that,
for every `n ≥ 1` and all `ε, δ > 0`:
* on every disorder `G` and every real `β` with `|β| ≤ β_*`, the run of `P` on the input
  `(n, γ, G, ε, δ, β)` has halted within `C + (n/(εδ))^C` charged steps (preprocessing
  included);
* there is a measurable set of disorders of probability at least `1 − ζ_n − δ` on which the
  returned value `Ẑ_G(β)` satisfies `|Ẑ_G(β)/Z_G(β) − 1| ≤ ε` simultaneously for all
  `|β| ≤ β_*`. -/
theorem theorem_1_2 (pmax : ℕ) (hpmax : 2 ≤ pmax) (γ : ℕ → ℝ) (hγ : NonzeroMixture pmax γ)
    (βstar : ℝ) (hβ0 : 0 < βstar) (hβ : βstar < beta2nd pmax γ) :
    ∃ (P : Program) (C : ℕ) (ζ : ℕ → ℝ), Admissible P ∧ Tendsto ζ atTop (𝓝 0) ∧
      ∀ n : ℕ, 1 ≤ n → ∀ ε δ : ℝ, 0 < ε → 0 < δ →
        let T : ℕ := ⌊(C : ℝ) + ((n : ℝ) / (ε * δ)) ^ C⌋₊
        (∀ (G : Disorder n pmax) (β : ℝ), |β| ≤ βstar →
          (run P (initialState n pmax γ G ε δ β) T).halted = true) ∧
        ∃ S : Set (Disorder n pmax), MeasurableSet S ∧
          (∀ G ∈ S, ∀ β : ℝ, |β| ≤ βstar →
            |output (run P (initialState n pmax γ G ε δ β) T) /
                partitionFunction n pmax γ G β - 1| ≤ ε) ∧
          ENNReal.ofReal (1 - ζ n - δ) ≤ disorderLaw n pmax S := by sorry

end MixedSpinColorCoding.Counting
