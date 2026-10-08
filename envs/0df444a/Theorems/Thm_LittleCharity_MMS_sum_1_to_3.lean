-- Prove2me | Theorems.Thm_LittleCharity_MMS_sum_1_to_3
-- name    : LittleCharity.MMS.sum_1_to_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T09:28:23.95047+00:00
-- url     : https://prove2.me/theorems/007e5193-9b2f-443c-90df-cc6b4786159f
-- title:
--   Proof of Theorem 14, p. 15 — summing (1)–(3): (2(n′−(k+1))+k+2)·v_i(X_i) ≥ v_i(M′ ∪ P)
-- statement:
--   Let the valuations be additive and let $X$ be a partial allocation with pool $P$, $k=|P|$, such that
--   1. $X$ is EFX;
--   2. $v_j(X_j)\ge v_j(P)$ for every agent $j$;
--   3. $|P|$ is less than the number of sources of the envy graph $G_X$.
--
--   Fix an agent $i$. Let $N'$ be the set consisting of all sources of $G_X$, agent $i$ and all agents $j$ with $|X_j|\ge 2$; let $n'=|N'|$ and let $M'=\bigcup_{j\in N'}X_j$ be the goods allocated to the agents in $N'$. Then
--   $$\bigl(2(n'-(k+1))+k+2\bigr)\, v_i(X_i)\ =\ (2n'-k)\, v_i(X_i)\ \ge\ v_i(M'\cup P).$$
--
--   This is the counting step of the proof of Theorem 14: it sums $v_i(X_i)\ge v_i(P)$ (1), $v_i(X_i)\ge v_i(X_j)$ for the sources $j$ (2) and $2v_i(X_i)\ge v_i(X_j)$ for the other $j\in N'$ (3), using that there are at least $k+1$ sources.
--
--   **Formalization Note** The set $N'$ is given by an equation fixing it to the set the page constructs. The coefficient is written in its simplified form $2n'-k$ as a real number (cardinalities cast to $\mathbb{R}$); it equals the printed $2(n'-(k+1))+k+2$.
-- source:
--   Chaudhury, Kavitha, Mehlhorn & Sgouritsa, A Little Charity Guarantees Almost Envy-Freeness, arXiv:1907.04596v3, p. 15, proof of Theorem 14, inequalities (1)–(3) and the sentence after them

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting

namespace LittleCharity.MMS

/-- Proof of Theorem 14, p. 15, summing (1)–(3): with `N'` the LittleCharity.EFX.sources of `G_X`, agent `i` and
every agent `j` with `|X_j| ≥ 2`, `M' = ⋃_{j ∈ N'} X_j`, `n' = |N'|` and `k = |P|`,
`(2(n' − (k+1)) + k + 2)·v_i(X_i) = (2n' − k)·v_i(X_i) ≥ v_i(M' ∪ P)`. -/
theorem sum_1_to_3 {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (hadd : IsAdditive v)
    (X : Fin n → Finset (Fin m)) (hX : LittleCharity.EFX.IsPartialAllocation X) (hEFX : IsEFX v X)
    (hpool : ∀ i, v i (LittleCharity.EFX.pool X) ≤ v i (X i))
    (hsrc : (LittleCharity.EFX.pool X).card < (LittleCharity.EFX.sources v X).card) (i : Fin n)
    (N' : Finset (Fin n))
    (hN' : N' = LittleCharity.EFX.sources v X ∪ {i} ∪ Finset.univ.filter (fun j => 2 ≤ (X j).card)) :
    v i (N'.biUnion X ∪ LittleCharity.EFX.pool X) ≤
      (2 * (N'.card : ℝ) - ((LittleCharity.EFX.pool X).card : ℝ)) * v i (X i) := by sorry

end LittleCharity.MMS
