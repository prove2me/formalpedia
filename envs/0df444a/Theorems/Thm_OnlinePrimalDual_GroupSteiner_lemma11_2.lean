-- Prove2me | Theorems.Thm_OnlinePrimalDual_GroupSteiner_lemma11_2
-- name    : OnlinePrimalDual.GroupSteiner.lemma11_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-21T05:58:37.63532+00:00
-- url     : https://prove2.me/theorems/85b54b0c-7f29-48a5-b9b6-09c7c4aedec3
-- title:
--   Lemma 11.2 — expected cost of the rounding algorithm's random cover
-- statement:
--   Given Lemma 11.1's marginal guarantee, the expected cost of the random cover `C` is at most
--   `∑_{e ∈ T} c_e w'_e`, the fractional cost at the end of the iteration.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 230, Lemma 11.2

import Mathlib
import Definitions.Def_OnlinePrimalDual_GroupSteiner_RandomCover
import Definitions.Def_OnlinePrimalDual_GroupSteiner_marg
import Definitions.Def_OnlinePrimalDual_GroupSteiner_RoundedTree
import Definitions.Def_OnlinePrimalDual_GroupSteiner_expectedCost

namespace OnlinePrimalDual.GroupSteiner

/-- **Lemma 11.2** (p. 230, PDF p. 141). "The next lemma follows from linearity of expectation":
given Lemma 11.1's marginal guarantee (`hmarg : ∀ e, ρ.marg e = w' e`), the expected cost of the
random cover `C` (drawn from `ρ`) is at most `∑_{e ∈ T} cₑ w'ₑ`, where `w'ₑ` is the weight of
edge `e` at the end of the iteration. -/
theorem lemma11_2 {E : Type*} [Fintype E] [DecidableEq E] (tr : RoundedTree E) (ρ : RandomCover E)
    (w' : E → ℝ) (hmarg : ∀ e, ρ.marg e = w' e) :
    ρ.expectedCost tr.cost ≤ ∑ e, tr.cost e * w' e := by sorry

end OnlinePrimalDual.GroupSteiner
