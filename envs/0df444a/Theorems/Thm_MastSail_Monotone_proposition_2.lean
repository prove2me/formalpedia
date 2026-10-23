-- Prove2me | Theorems.Thm_MastSail_Monotone_proposition_2
-- name    : MastSail.Monotone.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:34:40.588136+00:00
-- url     : https://prove2.me/theorems/58d79048-9919-43ec-a198-c904bccd790b
-- title:
--   Proposition 2, p. 14 — the mast: B^SO = {s = i ≥ i_m} with i_m ∈ (0, Ī]
-- statement:
--   Assume the standing assumptions of the model, valid weights $\omega$ and a trigger $t$ with $0<t\le\varphi^{SO}(\bar I)$. Let $i_m$ be the mast's foot and $B^{SO}$ the stockout bonus region of the plan (11). Then $i_m\in(0,\bar I]$ and
--   $$B^{SO}=\{(i,s): s=i,\ i_m\le i\le\bar I\}.$$
--
--   This is the "mast" shape of the stockout bonus region, Figure 1(b).
--
--   **Formalization Note** The hypothesis $t\le\varphi^{SO}(\bar I)$ is the proof's claim that $(\bar I,\bar I)$ lies in every bonus region (p. oa6), which the paper does not prove and without which no $i_m\le\bar I$ works. $t>0$ is added for $i_m>0$, since $\varphi^{SO}(0)\le0$. The statement concerns the canonical $i_m$ (least $i$ with $\varphi^{SO}(i)\ge t$).
-- source:
--   Dai, Ke & Ryan, SSRN 3235866, p. 14, Proposition 2 (proof pp. oa5–oa6)

import Mathlib
import Definitions.Def_MastSail_Monotone_Model

namespace MastSail.Monotone
theorem proposition_2 (M : Model) (hM : M.Standing) (ω : Weights) (hω : ω.Valid) (t : ℝ)
    (ht : 0 < t) (htI : t ≤ phiSO M ω M.Ibar) :
    0 < iM M ω t ∧ iM M ω t ≤ M.Ibar ∧
    bonusSO M ω t = {p : ℝ × ℝ | p.2 = p.1 ∧ iM M ω t ≤ p.1 ∧ p.1 ≤ M.Ibar} := by sorry
end MastSail.Monotone
