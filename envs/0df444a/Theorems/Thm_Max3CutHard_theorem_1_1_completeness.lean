-- Prove2me | Theorems.Thm_Max3CutHard_theorem_1_1_completeness
-- name    : Max3CutHard.theorem_1_1_completeness
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:50:19.641415+00:00
-- url     : https://prove2.me/theorems/adf5c90a-7603-40ff-85e9-9b62e6fe5f3f
-- title:
--   Proof of Theorem 1.1 — completeness: $w(J)=20$ and $\max\mathrm{cut}\ge(29/30-\tfrac95\varepsilon)\,w(J)$
-- statement:
--   Let $\Phi$ be a balanced role-separated instance (weights $\lambda_e\ge0$ summing to $1$) and $J=J(\Phi)$ the reduction graph for the family $(2E,N,N)$. Then
--
--   $$w(J)=\tfrac13(36+12+12)=20,$$
--
--   and if $\mathrm{val}(\Phi)\ge1-\varepsilon$,
--
--   $$\max_\chi\mathrm{cut}_\chi(J)\ \ge\ \Big(\frac{29}{30}-\frac95\varepsilon\Big)w(J).$$
--
--   This is the completeness half of the proof of Theorem 1.1.
--
--   Differences from the source:
--   - generalization: ε > 0 (the ε of Theorem 2.1) → every real ε; reason: the source's ε > 0 is the special case; ε = 0 is included, and for ε < 0 the hypothesis on val(Φ) cannot hold (1/3 ≤ val(Φ) ≤ 1 for every weighted role-separated instance)
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Proof of Theorem 1.1, completeness, p.6

import Mathlib
import Definitions.Def_Max3CutHard_J
import Definitions.Def_Max3CutHard_family0
import Definitions.Def_Max3CutHard_wR
import Definitions.Def_Max3CutHard_maxCutR
import Definitions.Def_Max3CutHard_WInst_IsWeighting
import Definitions.Def_Max3CutHard_WInst_Balanced
import Definitions.Def_Max3CutHard_WInst_val

namespace Max3CutHard

/-- **Proof of Theorem 1.1, completeness.** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Proof of Theorem 1.1, p.6: "Let `Φ` be an
instance from Theorem 2.1 and `J = J(Φ)`, so `w(J) = (1/3)(36 + 12 + 12) = 20`. Completeness: by
(1), `max_χ cut_χ(J) ≥ (1/3)(36 + 11 + 11) − 36ε = 58/3 − 36ε = (29/30 − (9/5)ε) w(J)`."

**Formalization Note.** `J` is built from the family `(2E, N, N)`; `Φ` is any balanced weighted
role-separated instance, `ε` any real. -/
theorem theorem_1_1_completeness {U W : Type} [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W]
    (Φ : WInst U W) (hΦ : Φ.IsWeighting) (hbal : Φ.Balanced) :
    wR (J Φ family0) = 20 ∧
    ∀ ε : ℝ, 1 - ε ≤ Φ.val →
      (29 / 30 - 9 / 5 * ε) * wR (J Φ family0) ≤ maxCutR 3 (J Φ family0) := by sorry

end Max3CutHard
