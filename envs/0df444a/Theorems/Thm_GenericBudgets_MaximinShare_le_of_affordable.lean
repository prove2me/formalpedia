-- Prove2me | Theorems.Thm_GenericBudgets_MaximinShare_le_of_affordable
-- name    : GenericBudgets.MaximinShare.le_of_affordable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T04:30:58.561367+00:00
-- url     : https://prove2.me/theorems/015d4408-fe9a-48c0-8cb5-75b47161f06a
-- title:
--   Proof of Proposition 3.2 — an affordable bundle cannot be preferred
-- statement:
--   Let an agent with valuation $w$ and budget $\beta$ demand bundle $S$ at prices $p$. If another bundle $T$ is affordable, $p(T)\le\beta$, then it cannot be strictly preferred to $S$:
--
--   $$
--   w(T)\le w(S).
--   $$
--
--   This connects the price bound for a chosen set of parts to the valuation comparison in the maximin guarantee. It applies to arbitrary cardinal valuations.
-- source:
--   Babaioff, Nisan and Talgam-Cohen, Competitive Equilibrium with Indivisible Goods and Generic Budgets, arXiv:1703.08150v2, p. 9, proof of Proposition 3.2, final three sentences

import Mathlib
import Definitions.Def_GenericBudgets_MaximinShare_Setting

namespace GenericBudgets.MaximinShare

/-- Proof of Proposition 3.2, p. 9: demand rules out a strictly preferred
affordable bundle. -/
theorem le_of_affordable {m : ℕ} (w : Finset (Fin m) → ℝ) (β : ℝ)
    (p : Fin m → ℝ) (S T : Finset (Fin m))
    (hDemand : GenericBudgets.AlmostEqual.IsDemanded w β p S) (hT : GenericBudgets.AlmostEqual.price p T ≤ β) : w T ≤ w S := by sorry

end GenericBudgets.MaximinShare
