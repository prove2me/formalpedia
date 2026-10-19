-- Prove2me | Theorems.Thm_OAI_FiniteEntropySeparation_Model_matrixHeatLaw_totalSecond_tendsto
-- name    : OAI.FiniteEntropySeparation.Model.matrixHeatLaw_totalSecond_tendsto
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T01:11:24.29484+00:00
-- url     : https://prove2.me/theorems/a1743c87-b0e2-4e1c-bc92-6973e71aef3c
-- title:
--   Total second moments of Gaussian-smoothed matrix microstate laws converge to those of the free heat flow of OpenAI's model (OpenAI finite-entropy separation)
-- statement:
--   **The model** (definitions bundle `OAIQWFE000` of this split). For $p \ne 0$ (`[NeZero p]`), `Model.τ p` is the vacuum tracial vector of OpenAI's Hilbert space `Model.H p`, `Model.X p h` $=$ `heatTuple (C p) (initialNoise p) h` (the $(p+1)$-tuple $C_i + \sqrt h\,S_i$ of $p$ semicircular operators and the operator `equidiscreteSignal p`, plus semicircular noise), and `Model.auxiliaryNoise p` the semicircular operators on the other $p+1$ noise labels.
--
--   **Matrix side.** `MatrixCoordinates n d` is the space of real coordinates of $n$-tuples of $d \times d$ Hermitian matrices, and `matrixMoment a w` is the normalized trace $\frac1d\operatorname{tr}$ of the product of the matrices of $a$ along the word $w$ (published bundle `Def_FiniteEntropySeparation`). `diagonalMicrostates τ X R k d` is `microstates τ X R k d (1/(k+1))` (bundle `OAIQWFE000`). For a measure $\mu$ on `MatrixCoordinates n d` and $s \in \mathbb R$, `matrixHeatLaw μ s` is Lebesgue measure with density `smoothedDensity μ (s/d)`, the density of $\mu$ convolved with the centered Gaussian kernel of variance parameter $s/d$ (bundle `OAIQWFE002`). For a moment functional $m$ on words in $n$ letters, `totalSecond m` $= \sum_i \operatorname{Re} m([i, i])$ (bundle `OAIQWFE001`).
--
--   **Statement.** Let $p \ne 0$, $D : \mathbb N \to \mathbb N$ with $D(k) > 0$ and $D(k) \to \infty$, and $h, R \in \mathbb R$ with $R \ge 0$ such that `diagonalMicrostates (τ p) (X p h) R k (D k)` is nonempty for every $k$. Let $\mu_k$ be probability measures on `MatrixCoordinates (p+1) (D k)` such that $\mu_k$-almost every point lies in that set. Then for every $s > 0$,
--   $$\int \mathrm{totalSecond}(\mathrm{matrixMoment}\ a)\ d\,\mathrm{matrixHeatLaw}(\mu_k, s)(a) \;\xrightarrow[k\to\infty]{}\; \mathrm{totalSecond}\Bigl(\mathrm{wordMoment}\bigl(\tau_p,\ \mathrm{heatTuple}(X_p(h), \mathrm{auxiliaryNoise}_p, s)\bigr)\Bigr).$$
--
--   Lean: `OAI.FiniteEntropySeparation.Model.matrixHeatLaw_totalSecond_tendsto`, OpenAI's theorem of that name (in `lean/OAI/Analysis/FreeEntropy/TerminalGaussian.lean`). `wordMoment`, `heatTuple`, `microstates`, `matrixMoment`, `hermitianMatrix`, `matrixOpNorm` and `MatrixCoordinates` come from the published bundle `Def_FiniteEntropySeparation`; `Model.τ`, `Model.X`, `Model.auxiliaryNoise`, `diagonalMicrostates` and `smoothedDensity` from the definitions bundle `OAIQWFE000`, `totalSecond` from `OAIQWFE001` and `matrixHeatLaw` from `OAIQWFE002`, of this split.
-- source:
--   OpenAI, A finite-entropy separation of microstates and nonmicrostates free entropy, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 298; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FreeEntropy/TerminalGaussian.lean (declaration OAI.FiniteEntropySeparation.Model.matrixHeatLaw_totalSecond_tendsto)

import Mathlib
import Definitions.Def_FiniteEntropySeparation
import Definitions.Def_OAIQWFE002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Finset Set
open scoped Topology
namespace FiniteEntropySeparation
namespace Model
variable (p : ℕ) [NeZero p]
variable {D : ℕ → ℕ} (hD0 : ∀k,0<D k) (hD : Tendsto D atTop atTop)
  {h R : ℝ} (hR : 0≤R) (hn : ∀k,(diagonalMicrostates (τ p) (X p h) R k (D k)).Nonempty)
  (μ : (k:ℕ) → Measure (MatrixCoordinates (p+1) (D k))) [∀k,IsProbabilityMeasure (μ k)]
  (hμ : ∀k,∀ᵐa ∂μ k,a∈diagonalMicrostates (τ p) (X p h) R k (D k))
include hD0 hD hR hn hμ in
 theorem matrixHeatLaw_totalSecond_tendsto {s : ℝ} (hs : 0<s) :
    Tendsto (fun k => ∫a,totalSecond (matrixMoment a) ∂matrixHeatLaw (μ k) s) atTop
      (𝓝 (totalSecond (wordMoment (τ p) (heatTuple (X p h) (auxiliaryNoise p) s)))) := by
  sorry
end Model

end FiniteEntropySeparation

end

end OAI
end
