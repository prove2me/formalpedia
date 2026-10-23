-- Prove2me | Theorems.Thm_MastSail_Monotone_proposition_1
-- name    : MastSail.Monotone.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:34:31.926702+00:00
-- url     : https://prove2.me/theorems/7b4c6d99-8285-49e9-8794-db30dc26fe58
-- title:
--   Proposition 1, p. 14 — the sail: B^NSO = {i ≥ i_s, s*(i) ≤ s < i} with s* nonincreasing and continuous, i_s ∈ (0, Ī]
-- statement:
--   Assume the standing assumptions of the model, strict MLRP of the demand densities, valid weights $\omega$ (nonnegative, summing to $1$) and a trigger $t>0$. Let $i_s$, $s^*$ and $B^{NSO}$ be the critical inventory, the sail boundary and the no-stockout bonus region of the plan (11). Then $i_s\in(0,\bar I]$, the function $s^*$ is nonincreasing and continuous on $[i_s,\bar I]$, and
--   $$B^{NSO}=\{(i,s): i_s\le i\le\bar I,\ s^*(i)\le s<i\}.$$
--
--   This is the "sail" shape of the no-stockout bonus region, Figure 1(a).
--
--   **Formalization Note** The paper asserts that some $s^*$ and $i_s$ exist; the statement is about the canonical $i_s$ and $s^*$ of (OA8)–(OA10) and so implies it. Strict MLRP of $g$ is added because continuity of $s^*$ fails under weak MLRP (a flat demand ratio makes $s^*$ jump). $t>0$ is added for $i_s>0$: MLRP and normalization give $\varphi^{NSO}(0,0)\le0$, so for $t\le0$ one has $i_s=0$. When the sail is empty, $i_s=\bar I$ (footnote 7) and the right-hand set is empty.
-- source:
--   Dai, Ke & Ryan, SSRN 3235866, p. 14, Proposition 1 (proof pp. oa4–oa5)

import Mathlib
import Definitions.Def_MastSail_Monotone_Model

namespace MastSail.Monotone
theorem proposition_1 (M : Model) (hM : M.Standing) (hg : M.StrictMLRPg) (ω : Weights)
    (hω : ω.Valid) (t : ℝ) (ht : 0 < t) :
    0 < iS M ω t ∧ iS M ω t ≤ M.Ibar ∧
    AntitoneOn (sStar M ω t) (Set.Icc (iS M ω t) M.Ibar) ∧
    ContinuousOn (sStar M ω t) (Set.Icc (iS M ω t) M.Ibar) ∧
    bonusNSO M ω t =
      {p : ℝ × ℝ | iS M ω t ≤ p.1 ∧ p.1 ≤ M.Ibar ∧ sStar M ω t p.1 ≤ p.2 ∧ p.2 < p.1} := by sorry
end MastSail.Monotone
