-- Prove2me | Theorems.Thm_LittleCharity_MMS_mms_le_average
-- name    : LittleCharity.MMS.mms_le_average
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T09:28:11.095668+00:00
-- url     : https://prove2.me/theorems/775f066e-c1db-4de8-bd24-2333cb3c769c
-- title:
--   §3, p. 14 — for additive valuations the maximin share is at most the proportional share: MMS_i(k, S) ≤ v_i(S)/k
-- statement:
--   Let the valuations be additive, let $i$ be an agent, $S$ a set of goods and $k\ge 1$. Then
--   $$\mathrm{MMS}_i(k,S)\ \le\ \frac{v_i(S)}{k}.$$
--
--   The paper states this for $(n,M)$: "the inequality $\mathrm{MMS}_i(n,M)\le v_i(M)/n$ holds for additive valuations", and the proof of Theorem 14 uses it for the sub-instance $(n', M'\cup P)$. It bounds the maximin share by the proportional share.
--
--   **Formalization Note** Stated for an arbitrary number $k\ge 1$ of bundles and an arbitrary set $S$ of goods, which covers both uses; $k$ is cast to $\mathbb{R}$ before dividing.
-- source:
--   Chaudhury, Kavitha, Mehlhorn & Sgouritsa, A Little Charity Guarantees Almost Envy-Freeness, arXiv:1907.04596v3, p. 14, §3.1, the sentence after the display ('MMS_i(n, M) ≤ v_i(M)/n holds for additive valuations'); used on p. 15 in the proof of Theorem 14

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting

namespace LittleCharity.MMS

/-- §3, p. 14: for additive valuations the maximin share of `S` over `k ≥ 1` bundles is at most
the average `v_i(S)/k`. -/
theorem mms_le_average {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (hadd : IsAdditive v)
    (i : Fin n) (k : ℕ) (hk : 0 < k) (S : Finset (Fin m)) :
    mms (v i) k S ≤ v i S / (k : ℝ) := by sorry

end LittleCharity.MMS
