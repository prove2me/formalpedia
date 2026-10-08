-- Prove2me | Theorems.Thm_LittleCharity_MMS_proposition_13
-- name    : LittleCharity.MMS.proposition_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T09:28:10.669021+00:00
-- url     : https://prove2.me/theorems/3fc89ed1-2714-4e3d-8aed-a9b48121bbe0
-- title:
--   Proposition 13 ([20]), p. 14 — removing agents and at most as many goods does not lower a remaining agent's maximin share
-- statement:
--   Let $N$ be a set of $n$ agents with additive valuations and $M$ a set of $m$ goods. Let $N'\subseteq N$ and $M'\subseteq M$ satisfy $|N\setminus N'|\ge |M\setminus M'|$, and put $n'=|N'|$. Then for every agent $i\in N'$,
--   $$\mathrm{MMS}_i(n',M')\ \ge\ \mathrm{MMS}_i(n,M).$$
--
--   In words: excluding some agents together with at most as many goods can only increase the maximin share of any agent who remains. The paper quotes this from [20] (Garg, McGlaughlin and Taki, SOSA 2019) without proof; it is the reduction that lets the proof of Theorem 14 (and of Theorem 16) pass to a smaller instance.
--
--   **Formalization Note** $N$ and $M$ are arbitrary finite sets of agents and goods of an ambient instance (`Finset (Fin n)`, `Finset (Fin m)`), not necessarily all agents and goods, as the applications in the paper require. Since $i\in N'$, both $n'$ and $n$ are at least 1, so the maximin shares are genuine.
-- source:
--   Chaudhury, Kavitha, Mehlhorn & Sgouritsa, A Little Charity Guarantees Almost Envy-Freeness, arXiv:1907.04596v3, p. 14, Proposition 13 (quoted from [20])

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting

namespace LittleCharity.MMS

/-- Proposition 13 ([20]), p. 14: deleting no more goods than agents cannot lower a remaining agent's maximin share. -/
theorem proposition_13 {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (hadd : IsAdditive v)
    (N N' : Finset (Fin n)) (M M' : Finset (Fin m)) (hN : N' ⊆ N) (hM : M' ⊆ M)
    (hcard : (M \ M').card ≤ (N \ N').card) (i : Fin n) (hi : i ∈ N') :
    mms (v i) N.card M ≤ mms (v i) N'.card M' := by sorry

end LittleCharity.MMS
