-- Prove2me | Theorems.Thm_OAI_FiniteEntropySeparation_chosen_terminal_gaussian
-- name    : OAI.FiniteEntropySeparation.chosen_terminal_gaussian
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T01:11:38.733089+00:00
-- url     : https://prove2.me/theorems/c7116cb2-8fa2-479a-883d-e91bdd49a1f1
-- title:
--   For OpenAI's chosen model, normalized entropies of smoothed matrix microstate laws eventually fall 1 below the Gaussian entropy (OpenAI finite-entropy separation)
-- statement:
--   **Definitions** (as in the statements `OAI.FiniteEntropySeparation.Model.matrixHeatLaw_blocks_eventually` and `OAI.FiniteEntropySeparation.Model.chiStar_tail_formula` of this split). `chosenP` $= 2^{64}$ and `chosenTime` $= 2^{48}$. `Model.τ p`, `Model.X p h` are OpenAI's model tracial vector and $(p+1)$-tuple; `equidiscreteAtom`, `spectralBasis` and `spectralGood` are the spectral parameters; `MatrixCoordinates`, `diagonalMicrostates τ X R k d` $=$ `microstates τ X R k d (1/(k+1))` describe matrix microstates; `Model.gaussianEntropy p a` $= \frac{p+1}{2}\log(2\pi e) + \frac12\sum_i\log(a + \mathrm{variance}_i)$. For a measure $\mu$ on `MatrixCoordinates n d`, `normalizedMatrixEntropy μ s` $= $ `classicalEntropy μ (s/d)` $/d^2 + \frac n2\log d$, where `classicalEntropy μ s` $= -\int \rho\log\rho$ for the Gaussian-smoothed density $\rho = $ `smoothedDensity μ s`.
--
--   **Statement.** Let $P = $ `chosenP` and $T = $ `chosenTime`. Let $D : \mathbb N \to \mathbb N$ with $D(k) > 0$ and $D(k) \to \infty$, and $h, R, \delta, \Delta$ real numbers with $0 < h < 1$, $R \ge 0$, $\delta, \Delta > 0$, $\delta \le \Delta/4$. Assume distinct atoms `equidiscreteAtom P` are at distance at least $\Delta$, that $\frac34 \le (\mathrm{spectralBasis}_P\ l)(r)^2$ whenever $|r - \mathrm{atom}_l| \le \delta$, and `spectralGood P δ Δ (wordMoment (τ P) (X P h))`. Assume `diagonalMicrostates (τ P) (X P h) R k (D k)` is nonempty for every $k$, and let $\mu_k$ be probability measures on `MatrixCoordinates (P+1) (D k)` with $\mu_k$-almost every point in it. Then for all sufficiently large $k$,
--   $$\mathrm{normalizedMatrixEntropy}(\mu_k, T) \;\le\; \mathrm{gaussianEntropy}_P(h + T) - 1.$$
--
--   Lean: `OAI.FiniteEntropySeparation.chosen_terminal_gaussian`, OpenAI's theorem of that name (in `lean/OAI/Analysis/FreeEntropy/GaussianCorrection.lean`). `wordMoment`, `heatTuple`, `microstates` and `MatrixCoordinates` come from the published bundle `Def_FiniteEntropySeparation`; `chosenP`, `chosenTime`, `Model.τ`, `Model.X`, `Model.gaussianEntropy`, `equidiscreteAtom`, `diagonalMicrostates`, `smoothedDensity` and `classicalEntropy` from the definitions bundle `OAIQWFE000`, and `spectralBasis`, `spectralGood` and `normalizedMatrixEntropy` from `OAIQWFE002`, of this split.
-- source:
--   OpenAI, A finite-entropy separation of microstates and nonmicrostates free entropy, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 298; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FreeEntropy/GaussianCorrection.lean (declaration OAI.FiniteEntropySeparation.chosen_terminal_gaussian)

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
 theorem chosen_terminal_gaussian {D : ℕ → ℕ} (hD0 : ∀k,0<D k) (hD : Tendsto D atTop atTop)
    {h R δ Δ : ℝ} (hh0 : 0<h) (hh1 : h<1) (hR : 0≤R)
    (hδ : 0<δ) (hΔ : 0<Δ) (hδΔ : δ≤Δ/4)
    (hsep : ∀i j : Fin chosenP,i≠j → Δ≤|equidiscreteAtom chosenP i-equidiscreteAtom chosenP j|)
    (hq : ∀l : Fin chosenP,∀r : ℝ,|r-equidiscreteAtom chosenP l|≤δ → (3:ℝ)/4≤((spectralBasis chosenP l).eval r)^2)
    (hh : spectralGood chosenP δ Δ (wordMoment (Model.τ chosenP) (Model.X chosenP h)))
    (hn : ∀k,(diagonalMicrostates (Model.τ chosenP) (Model.X chosenP h) R k (D k)).Nonempty)
    (μ : (k:ℕ) → Measure (MatrixCoordinates (chosenP+1) (D k))) [∀k,IsProbabilityMeasure (μ k)]
    (hμ : ∀k,∀ᵐa ∂μ k,a∈diagonalMicrostates (Model.τ chosenP) (Model.X chosenP h) R k (D k)) :
    ∀ᶠk in atTop,normalizedMatrixEntropy (μ k) chosenTime≤Model.gaussianEntropy chosenP (h+chosenTime)-1 := by
  sorry
end FiniteEntropySeparation

end

end OAI
end
