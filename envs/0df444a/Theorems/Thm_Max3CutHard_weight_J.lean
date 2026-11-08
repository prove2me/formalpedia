-- Prove2me | Theorems.Thm_Max3CutHard_weight_J
-- name    : Max3CutHard.weight_J
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T06:49:29.035649+00:00
-- url     : https://prove2.me/theorems/ad20d490-34e4-496b-871c-aee98bae798c
-- title:
--   Section 2 — the total weight of $J(\Phi)$ for balanced $\Phi$
-- statement:
--   Let $(I_0,I_1,I_2)$ be a family of gadgets with non-negative weights and let $\Phi$ be a balanced role-separated instance (weights $\lambda_e\ge0$ summing to $1$). Then the reduction graph satisfies
--
--   $$w(J(\Phi))=\frac13\sum_{t\in\mathbb Z_3}w(I_t).$$
--
--   Differences from the source:
--   - generalization: k ≥ 3 fixed for gadgets → every k; reason: the identity holds for every k; k ≥ 3 is a special case
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Section 2, The reduction, p.5

import Mathlib
import Definitions.Def_Max3CutHard_J
import Definitions.Def_Max3CutHard_wR
import Definitions.Def_Max3CutHard_IsNonneg
import Definitions.Def_Max3CutHard_WInst_IsWeighting
import Definitions.Def_Max3CutHard_WInst_Balanced

namespace Max3CutHard

/-- **The total weight of `J(Φ)`.** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Section 2, The reduction, p.5: "whose auxiliary vertices
are new. For balanced `Φ`, `w(J) = (1/3) Σ_t w(I_t)`."

**Formalization Note.** Every `k`, every family of non-negatively weighted gadgets, and every
balanced weighted role-separated instance. -/
theorem weight_J {U W : Type} {k : ℕ} (F : Family k) (hF : ∀ t, IsNonneg (F t).edges)
    (Φ : WInst U W) (hΦ : Φ.IsWeighting) (hbal : Φ.Balanced) :
    wR (J Φ F) = (1 / 3) * ∑ t : ZMod 3, wR (F t).edges := by sorry

end Max3CutHard
