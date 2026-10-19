-- Prove2me | Theorems.Thm_OAI_FiniteEntropySeparation_chosen_chi_bound
-- name    : OAI.FiniteEntropySeparation.chosen_chi_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T01:12:38.280771+00:00
-- url     : https://prove2.me/theorems/9f967558-4456-4c31-9ede-d15aa3230cd6
-- title:
--   For OpenAI's chosen spectrally good model, the microstates free entropy is at most χ* − 1/2 (OpenAI finite-entropy separation)
-- statement:
--   **Definitions** (as in the statements `OAI.FiniteEntropySeparation.Model.chi_gt_bot`, `OAI.FiniteEntropySeparation.Model.chiStar_tail_formula` and `OAI.FiniteEntropySeparation.Model.matrixHeatLaw_blocks_eventually` of this split). `chosenP` $= 2^{64}$. `Model.τ p`, `Model.X p h` and `Model.auxiliaryNoise p` are OpenAI's model tracial vector, $(p+1)$-tuple and auxiliary semicircular noise (definitions bundle `OAIQWFE000`). `chi` is Voiculescu's microstates free entropy and `chiStar` the nonmicrostates free entropy along the free heat flow (published bundle `Def_FiniteEntropySeparation`). `equidiscreteAtom p l` $= -1 + 2l/(p-1)$, `spectralBasis p l` is the Lagrange basis polynomial at these atoms, and `spectralGood p δ Δ m` is OpenAI's spectral condition on a moment functional $m$ (bundles `OAIQWFE000`, `OAIQWFE002`).
--
--   **Statement.** Let $P = $ `chosenP` and $h, \delta, \Delta$ real numbers with $0 < h < 1$, $\delta > 0$, $\Delta > 0$ and $\delta \le \Delta/4$. Assume that distinct atoms are far apart, $\Delta \le |\mathrm{atom}_i - \mathrm{atom}_j|$ for $i \ne j$, that $\frac34 \le (\mathrm{spectralBasis}_P\ l)(r)^2$ whenever $|r - \mathrm{atom}_l| \le \delta$, and `spectralGood P δ Δ (wordMoment (τ P) (X P h))`. Then, in `EReal`,
--   $$\mathrm{chi}\bigl(\tau_P,\ X_P(h)\bigr) \;\le\; \mathrm{chiStar}\bigl(\tau_P,\ X_P(h),\ \mathrm{auxiliaryNoise}_P\bigr) - \tfrac12.$$
--
--   Lean: `OAI.FiniteEntropySeparation.chosen_chi_bound`, OpenAI's theorem of that name (in `lean/OAI/Analysis/FreeEntropy/CutoffSeparation.lean`). `chi`, `chiStar`, `chiCutoff`, `microstates`, `wordMoment` and `heatTuple` come from the published bundle `Def_FiniteEntropySeparation`; `chosenP`, `Model.τ`, `Model.X`, `Model.auxiliaryNoise` and `equidiscreteAtom` from the definitions bundle `OAIQWFE000`, and `spectralBasis` and `spectralGood` from `OAIQWFE002`, of this split.
-- source:
--   OpenAI, A finite-entropy separation of microstates and nonmicrostates free entropy, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 298; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FreeEntropy/CutoffSeparation.lean (declaration OAI.FiniteEntropySeparation.chosen_chi_bound)

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
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
namespace FiniteEntropySeparation
 theorem chosen_chi_bound {h δ Δ : ℝ} (hh0 : 0<h) (hh1 : h<1)
    (hδ : 0<δ) (hΔ : 0<Δ) (hδΔ : δ≤Δ/4)
    (hsep : ∀i j : Fin chosenP,i≠j → Δ≤|equidiscreteAtom chosenP i-equidiscreteAtom chosenP j|)
    (hq : ∀l : Fin chosenP,∀r : ℝ,|r-equidiscreteAtom chosenP l|≤δ → (3:ℝ)/4≤((spectralBasis chosenP l).eval r)^2)
    (hh : spectralGood chosenP δ Δ (wordMoment (Model.τ chosenP) (Model.X chosenP h))) :
    chi (Model.τ chosenP) (Model.X chosenP h)≤
      chiStar (Model.τ chosenP) (Model.X chosenP h) (Model.auxiliaryNoise chosenP)-(1/2:EReal) := by
  sorry
end FiniteEntropySeparation

end

end OAI
end
