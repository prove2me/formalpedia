-- Prove2me | Theorems.Thm_OAI_FiniteEntropySeparation_Model_heatFisher_shift_intervalIntegrable
-- name    : OAI.FiniteEntropySeparation.Model.heatFisher_shift_intervalIntegrable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T01:09:22.569386+00:00
-- url     : https://prove2.me/theorems/13c0fce2-a480-4b74-b342-9f8ec669c833
-- title:
--   The free Fisher information of OpenAI's model along the heat flow is interval integrable away from time zero (OpenAI finite-entropy separation)
-- statement:
--   **The model** (definitions bundle `OAIQWFE000` of this split). For $p \ne 0$ (`[NeZero p]`), `Model.τ p` is the vacuum tracial vector of OpenAI's Hilbert space `Model.H p`, `Model.C p` is the $(p+1)$-tuple of $p$ semicircular operators `semicircularB i` and the operator `equidiscreteSignal p`, and `Model.X p u` $=$ `heatTuple (C p) (initialNoise p) u`, i.e. $X_i = C_i + \sqrt u\,S_i$ with semicircular noise $S_i$. `Model.heatFisherReal p u` $=$ `(freeFisher (τ p) (X p u)).toReal`, the free Fisher information (published bundle `Def_FiniteEntropySeparation`) as a real number.
--
--   **Statement.** Let $p \ge 2$ and $h, a, t$ real numbers with $h > 0$ and $0 \le a \le t$. Then $s \mapsto$ `heatFisherReal p (h + s)` is interval integrable on $[a, t]$ for Lebesgue measure (`IntervalIntegrable … volume a t`).
--
--   Lean: `OAI.FiniteEntropySeparation.Model.heatFisher_shift_intervalIntegrable`, OpenAI's theorem of that name (in `lean/OAI/Analysis/FreeEntropy/ModelFlowLimit.lean`). `freeFisher` and `heatTuple` come from the published bundle `Def_FiniteEntropySeparation`; `Model.τ`, `Model.X` and `Model.heatFisherReal` from the definitions bundle `OAIQWFE000` of this split.
-- source:
--   OpenAI, A finite-entropy separation of microstates and nonmicrostates free entropy, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 298; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FreeEntropy/ModelFlowLimit.lean (declaration OAI.FiniteEntropySeparation.Model.heatFisher_shift_intervalIntegrable)

import Mathlib
import Definitions.Def_OAIQWFE000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace FiniteEntropySeparation.Model
variable (p : ℕ) [NeZero p]
 theorem heatFisher_shift_intervalIntegrable (hp : 2≤p) {h a t : ℝ}
    (hh : 0<h) (ha : 0≤a) (hat : a≤t) :
    IntervalIntegrable (fun s => heatFisherReal p (h+s)) volume a t := by
  sorry
end FiniteEntropySeparation.Model

end

end OAI
end
