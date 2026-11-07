-- Prove2me | Theorems.Thm_OptimalSpectrum_Entangled_theorem_1_1
-- name    : OptimalSpectrum.Entangled.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:24:02.733498+00:00
-- url     : https://prove2.me/theorems/52029921-b324-4dd1-8978-b67e7e9a3f53
-- title:
--   Theorem 1.1 — entangled spectrum estimation with $O(d^2\min\{(\varepsilon\log d)^{-4},(\varepsilon\log d)^{-2}\})$ copies
-- statement:
--   There is a universal constant $C>0$ such that for every dimension $d\ge2$ and every accuracy $0<\varepsilon<1$ there are a number of copies
--
--   $$n\le C\,d^2\min\Big\{\frac1{(\varepsilon\log d)^4},\frac1{(\varepsilon\log d)^2}\Big\}$$
--
--   and a measurement (POVM) $E$ on $(\mathbb C^d)^{\otimes n}$ with outcomes in the sorted probability vectors, chosen independently of the state, such that for every density matrix $\rho$ on $\mathbb C^d$ the outcome $\widehat\alpha$ of measuring $E$ on $\rho^{\otimes n}$ satisfies
--
--   $$\mathbb P\big[d_{\mathrm{TV}}(\widehat\alpha,\mathrm{spec}(\rho))\le\varepsilon\big]\ge0.99 .$$
--
--   Here $\mathrm{spec}(\rho)$ is the nonincreasing eigenvalue vector and $d_{\mathrm{TV}}(p,q)=\frac12\|p-q\|_1$. By Remark 1.2 of the paper this matches Wang's lower bound, so the rate is optimal.
--
--   **Formalization Note** The POVM is an arbitrary joint measurement of all copies with possibly continuous outcomes (Definition 4.1); the paper's two-stage Algorithm 8.1 is one such measurement, and $n$ counts all copies it uses.
--
--   Differences from the source:
--   - encoding: "there is a quantum algorithm … using O(d² min{…}) copies" → ∃ C > 0, ∀ d ≥ 2, ∀ ε ∈ (0,1), ∃ n ≤ C·d²·min{…}, ∃ POVM E on (ℂ^d)^⊗n with outcomes in sorted probability vectors, ∀ ρ; reason: Definition 4.1 entangled model with continuous outcomes; O(·) uniform in d and ε; E chosen before ρ
--   - encoding: log d, base unstated → Real.log (natural logarithm); reason: the base changes only C
--   - encoding: ρ ∈ C^(d×d) for every d → d ≥ 2; reason: at d = 1, log 1 = 0 and the printed bound is undefined; only that case is excluded
-- source:
--   Bakshi, Singh, Tan, Optimal spectrum estimation, arXiv:2609.30171, Theorem 1.1, p. 1 (PDF p. 3)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_GeneralPOVMs
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P38
import Definitions.Def_OptimalSpectrum_Entangled_spec
import Definitions.Def_OptimalSpectrum_Entangled_SortedProbVec
import Definitions.Def_OptimalSpectrum_Entangled_copiesLaw

open MeasureTheory
open QAlgorithms.Papers.Independent.Support50.P38 (tv)

namespace OptimalSpectrum.Entangled

/-- **Theorem 1.1 (Entangled spectrum estimation).**
Bakshi, Singh, Tan, *Optimal spectrum estimation*, arXiv:2609.30171, Theorem 1.1, printed p. 1 (PDF p. 3): "Given 0 < ε < 1 and an unknown quantum state
ρ ∈ C^(d×d), there is a quantum algorithm that outputs a sorted probability vector α̂ satisfying
d_TV(α̂, spec(ρ)) ⩽ ε with probability at least 0.99 using O(d² min{1/(ε log d)⁴, 1/(ε log d)²})
copies of ρ."

There is an absolute constant `C > 0` such that for every `d ≥ 2` and every `ε ∈ (0, 1)` there are a
copy count `n ≤ C d² min{(ε log d)⁻⁴, (ε log d)⁻²}` and a POVM `E` on `(ℂ^d)^{⊗n}`, chosen before the
state, with outcomes in the sorted probability vectors, such that for every density matrix `ρ` on
`ℂ^d` the outcome `x` satisfies `d_TV(x, spec ρ) ≤ ε` with probability at least `0.99`.

**Formalization Note.** A "quantum algorithm" in the entangled model is an arbitrary POVM on all
copies with possibly continuous outcomes (Definition 4.1, printed p. 11); the adaptive two-stage
Algorithm 8.1 is one such POVM. `log` is the natural logarithm (the paper's base is unstated and
changes only `C`). `d ≥ 2` excludes only `d = 1`, where `log 1 = 0` makes the printed bound
undefined. The event is closed, hence measurable. -/
theorem theorem_1_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d → ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ n : ℕ, (n : ℝ) ≤ C * (d : ℝ) ^ 2 *
          min (1 / (ε * Real.log d) ^ 4) (1 / (ε * Real.log d) ^ 2) ∧
        ∃ E : QAlgorithms.Measurements.OperatorPOVM (Fin n → Fin d) (SortedProbVec d),
          ∀ (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ),
            ENNReal.ofReal (99 / 100) ≤ copiesLaw E ρ hρ {x | tv x.val (spec ρ) ≤ ε} := by sorry

end OptimalSpectrum.Entangled
