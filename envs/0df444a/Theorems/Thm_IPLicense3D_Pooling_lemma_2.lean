-- Prove2me | Theorems.Thm_IPLicense3D_Pooling_lemma_2
-- name    : IPLicense3D.Pooling.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:25:36.925502+00:00
-- url     : https://prove2.me/theorems/f0eb429d-a71d-41e6-bbef-4212bd914bc9
-- title:
--   Lemma 2, p. 2694 — the royalty fee r̂ that equalizes the two buyers' surpluses
-- statement:
--   Consider two buyers with demand rates $\lambda_1 < \lambda_2$ and positive maximum surpluses $\bar S_1, \bar S_2 > 0$ (the standing assumption of §4.3.3), under the standing assumptions of §3. In Lean, Buyer 1 is index `0` and Buyer 2 is index `1`.
--
--   1. There is a unique $\hat r \ge 0$ with $S_1(0,\hat r) = S_2(0,\hat r)$ if and only if $\bar S_1 \le \bar S_2$.
--   2. Let $\hat r \ge 0$ solve $S_1(0,\hat r) = S_2(0,\hat r)$, and let $\bar r_1(0), \bar r_2(0) \ge 0$ be the maximum royalty fees, given by $S_1(0, \bar r_1(0)) = 0$ and $S_2(0, \bar r_2(0)) = 0$. Then
--   $$
--   S_i(0,\hat r) \ge 0 \text{ for } i = 1, 2 \iff \bar r_2(0) \le \bar r_1(0).
--   $$
--
--   The royalty $\hat r$ is where the two buyers' surpluses cross. Together with $\bar r_1(0)$ and $\bar r_2(0)$ it defines the case split of Table 1.
--
--   **Formalization Note** $\hat r$, $\bar r_1(0)$ and $\bar r_2(0)$ are bound by their defining equations; Corollary 1(i) and part 1 guarantee they exist and are unique.
-- source:
--   Zhang, Westerweel, Basten & Song, Distributed 3D Printing of Spare Parts via IP Licensing, MSOM 24(5) 2022, p. 2694, Lemma 2; proof p. 2700

import Mathlib
import Definitions.Def_IPLicense3D_Pooling_Model

namespace IPLicense3D.Pooling
open Model

theorem lemma_2 (M : Model 2) (hM : M.Standing) (hlam : M.lam 0 < M.lam 1)
    (hS0 : 0 < M.maxSurplus 0) (hS1 : 0 < M.maxSurplus 1) :
    ((∃! rh : ℝ, 0 ≤ rh ∧ M.surplus 0 0 rh = M.surplus 1 0 rh) ↔ M.maxSurplus 0 ≤ M.maxSurplus 1) ∧
    (∀ rh rb0 rb1 : ℝ, 0 ≤ rh → M.surplus 0 0 rh = M.surplus 1 0 rh →
      0 ≤ rb0 → M.surplus 0 0 rb0 = 0 → 0 ≤ rb1 → M.surplus 1 0 rb1 = 0 →
      ((0 ≤ M.surplus 0 0 rh ∧ 0 ≤ M.surplus 1 0 rh) ↔ rb1 ≤ rb0)) := by sorry

end IPLicense3D.Pooling
