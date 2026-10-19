-- Prove2me | Theorems.Thm_OAI_FiniteEntropySeparation_Model_chiStar_tail_formula
-- name    : OAI.FiniteEntropySeparation.Model.chiStar_tail_formula
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T01:08:59.925774+00:00
-- url     : https://prove2.me/theorems/68db28d4-5635-4741-8bdf-a3be0ecfdf63
-- title:
--   Tail formula for the nonmicrostates free entropy χ* of OpenAI's model tuple in terms of its Gaussian entropy and Fisher deficit (OpenAI finite-entropy separation)
-- statement:
--   **The model** (definitions bundle `OAIQWFE000` of this split). For $p \ne 0$ (`[NeZero p]`), `Model.τ p` is the vacuum tracial vector of OpenAI's Hilbert space `Model.H p`, `Model.C p` is the $(p+1)$-tuple of $p$ semicircular operators `semicircularB i` and the operator `equidiscreteSignal p`, and `Model.X p h` $=$ `heatTuple (C p) (initialNoise p) h`, i.e. $X_i = C_i + \sqrt h\,S_i$ with semicircular noise $S_i$ on the first $p+1$ noise labels. `Model.auxiliaryNoise p` is the $(p+1)$-tuple of semicircular operators on the other $p+1$ noise labels.
--
--   Further definitions:
--   - `Model.variance p i` $= \|C_i\,\Omega\|^2$ for the vacuum $\Omega$, `Model.gaussianEntropy p a` $= \frac{p+1}{2}\log(2\pi e) + \frac12\sum_{i} \log(a + \mathrm{variance}_i)$, and `Model.covarianceFisher p u` $= \sum_i (\mathrm{variance}_i + u)^{-1}$.
--   - `Model.fisherDeficit p u` $= $ `(freeFisher (τ p) (X p u)).toReal` $- $ `covarianceFisher p u`, with `freeFisher` the free Fisher information of the published bundle.
--   - `chiStar τ X S` (published bundle `Def_FiniteEntropySeparation`) is Voiculescu's nonmicrostates free entropy along the free heat flow $X + \sqrt s\,S$: with $n$ the length of the tuple, $b(s) = n/(1+s)$ and $f(s) = $ `freeFisher τ (heatTuple X S s)`, it is $\frac n2\log(2\pi e) + \frac12\int_0^\infty (b - f)^+ - \frac12\int_0^\infty (f - b)^+$ (the two lower Lebesgue integrals in $[0, \infty]$ converted to `EReal`).
--
--   **Statement.** Let $p \ge 2$ and $a > 0$. Then, in `EReal`,
--   $$\mathrm{chiStar}\bigl(\tau_p,\ X_p(a),\ \mathrm{auxiliaryNoise}_p\bigr) \;=\; \mathrm{gaussianEntropy}_p(a) - \tfrac12\int_a^\infty \mathrm{fisherDeficit}_p(u)\,du,$$
--   where the integral is the Bochner integral over the open half-line $(a, \infty)$ and the right side is a real number cast to `EReal`.
--
--   Lean: `OAI.FiniteEntropySeparation.Model.chiStar_tail_formula`, OpenAI's theorem of that name (in `lean/OAI/Analysis/FreeEntropy/EntropyDeficit.lean`). `chiStar`, `freeFisher` and `heatTuple` come from the published bundle `Def_FiniteEntropySeparation`; `Model.τ`, `Model.X`, `Model.auxiliaryNoise`, `Model.variance`, `Model.gaussianEntropy`, `Model.covarianceFisher` and `Model.fisherDeficit` from the definitions bundle `OAIQWFE000` of this split.
-- source:
--   OpenAI, A finite-entropy separation of microstates and nonmicrostates free entropy, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 298; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FreeEntropy/EntropyDeficit.lean (declaration OAI.FiniteEntropySeparation.Model.chiStar_tail_formula)

import Mathlib
import Definitions.Def_FiniteEntropySeparation
import Definitions.Def_OAIQWFE000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter Finset
namespace FiniteEntropySeparation.Model
variable (p : ℕ) [NeZero p]
theorem chiStar_tail_formula (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a) :
    chiStar (τ p) (X p a) (auxiliaryNoise p) =
      ((gaussianEntropy p a - (1/2 : ℝ) * ∫ u in Ioi a, fisherDeficit p u : ℝ) : EReal) := by
  sorry
end FiniteEntropySeparation.Model

end

end OAI
end
