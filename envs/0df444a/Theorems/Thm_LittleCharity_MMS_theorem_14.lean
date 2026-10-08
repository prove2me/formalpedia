-- Prove2me | Theorems.Thm_LittleCharity_MMS_theorem_14
-- name    : LittleCharity.MMS.theorem_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T09:28:06.17447+00:00
-- url     : https://prove2.me/theorems/b74bf3c1-0afa-4b64-becc-d983d5aceffe
-- title:
--   Theorem 14, p. 14 — an allocation meeting Theorem 8's three conditions gives every agent at least MMS_i(n, M)/(2 − |P|/n)
-- statement:
--   Let $N=[n]$ be a set of $n$ agents with additive valuations and $M$ a set of $m$ goods. Let $X=\langle X_1,\dots,X_n\rangle$ be a partial allocation with pool of unallocated goods $P=M\setminus\bigcup_i X_i$ and $k=|P|$, satisfying the three conditions of Theorem 8:
--   1. $X$ is EFX;
--   2. $v_i(X_i)\ge v_i(P)$ for all agents $i$;
--   3. $|P|$ is less than the number of sources (unenvied agents) of the envy graph $G_X$.
--
--   Then for every agent $i\in N$,
--   $$v_i(X_i)\ \ge\ \frac{\mathrm{MMS}_i(n,M)}{2-\frac{k}{n}} .$$
--
--   The guarantee interpolates between the factor $\tfrac12$ for an empty pool and the factor $\bigl(1+\tfrac1n\bigr)^{-1}$ when $|P|=n-1$: the more goods the algorithm leaves to charity, the closer every agent gets to her full maximin share.
--
--   **Formalization Note** The paper's Theorem 14 asserts that there exists an allocation satisfying Theorem 8's conditions, a ½-Nash-social-welfare guarantee, and this bound. Existence of such an allocation is Theorem 8 (the goal of mission I of this series); its proof of the third bullet uses only the three conditions, so the goal is posed as the implication for every such allocation, and combining it with Theorem 8 gives the printed bullet. The Nash-social-welfare bullet is not posed: it rests on Lemma 12, which initialises the algorithm with the allocation of [12], a black box not proved in the paper. Condition 3 forces $n\ge 1$ and $k<n$, so the denominator $2-k/n$ (computed in $\mathbb{R}$) exceeds 1 and $\mathrm{MMS}_i(n,M)$ uses $n\ge 1$ bundles. Agents are `Fin n`, 0-based.
-- source:
--   Chaudhury, Kavitha, Mehlhorn & Sgouritsa, A Little Charity Guarantees Almost Envy-Freeness, arXiv:1907.04596v3, p. 14, Theorem 14 (third bullet); conditions of Theorem 8, pp. 11–12; proof p. 15

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting

namespace LittleCharity.MMS

/-- Theorem 14, p. 14, third bullet: every allocation `X` with LittleCharity.EFX.pool `P = M \ ⋃ X_i` that meets
the three conditions of Theorem 8 (EFX; nobody envies `P`; `|P|` < number of LittleCharity.EFX.sources) gives every
agent `i` at least `MMS_i(n, M)/(2 − k/n)`, where `k = |P|`. -/
theorem theorem_14 {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (hadd : IsAdditive v)
    (X : Fin n → Finset (Fin m)) (hX : LittleCharity.EFX.IsPartialAllocation X) (hEFX : IsEFX v X)
    (hpool : ∀ i, v i (LittleCharity.EFX.pool X) ≤ v i (X i))
    (hsrc : (LittleCharity.EFX.pool X).card < (LittleCharity.EFX.sources v X).card) (i : Fin n) :
    mms (v i) n Finset.univ / (2 - ((LittleCharity.EFX.pool X).card : ℝ) / (n : ℝ)) ≤ v i (X i) := by sorry

end LittleCharity.MMS
