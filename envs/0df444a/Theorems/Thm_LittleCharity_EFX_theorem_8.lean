-- Prove2me | Theorems.Thm_LittleCharity_EFX_theorem_8
-- name    : LittleCharity.EFX.theorem_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:41:27.215988+00:00
-- url     : https://prove2.me/theorems/61b240a5-540f-42a1-9ee8-f31eb5f34ed1
-- title:
--   Theorem 8 — existence of an EFX allocation with bounded charity
-- statement:
--   Let there be $n\ge1$ agents with normalized and monotone valuations over a set $M$ of $m$ indivisible goods. Then there is an allocation $X=\langle X_1,\dots,X_n\rangle$ of pairwise disjoint bundles, with pool $P=M\setminus\bigcup_i X_i$ of unallocated goods, such that
--
--   1. $X$ is EFX: $v_i(X_j\setminus\{g\})\le v_i(X_i)$ for any agents $i,j$ and $g\in X_j$;
--   2. no agent envies the pool: $v_i(P)\le v_i(X_i)$ for all $i$;
--   3. the pool is smaller than the number of sources of the envy graph, and in particular smaller than $n$:
--   $$
--   |P|<\#\mathrm{sources}(G_X),\qquad |P|<n .
--   $$
--
--   Giving the pool away to charity therefore costs fewer than $n$ goods, none of which any agent prefers to her own bundle. The strong form $|P|<\#\mathrm{sources}$ is the one used to derive the paper's maximin-share and groupwise-maximin-share guarantees.
--
--   **Formalization Note** The hypothesis $n\ge1$ is added: with no agents the bound $|P|<n$ fails as soon as $m>0$, and the paper always has agents. Valuations are real-valued; nonnegativity follows from normalized plus monotone. The theorem's last sentence ("Algorithm 1 determines such an allocation in at most $nmV/\Delta$ iterations") is not posed: it requires a model of the algorithm's runs, and the count printed just before the theorem (at most $nV/\Delta$ applications of $U_1$/$U_2$ and at most $m$ successive applications of $U_0$ between them) gives $K+(K+1)m$ with $K\le nV/\Delta$, which can exceed $nmV/\Delta$.
-- source:
--   Chaudhury, Kavitha, Mehlhorn & Sgouritsa, A Little Charity Guarantees Almost Envy-Freeness, arXiv:1907.04596v3, pp. 11–12, Theorem 8

import Mathlib
import Definitions.Def_LittleCharity_EFX_Setting

namespace LittleCharity.EFX

theorem theorem_8 {n m : ℕ} (hn : 0 < n)
    (v : Fin n → Finset (Fin m) → ℝ)
    (hnorm : IsNormalized v) (hmono : IsMonotoneVal v) :
    ∃ X : Fin n → Finset (Fin m),
      IsPartialAllocation X ∧ IsEFX v X ∧
      (∀ i, v i (pool X) ≤ v i (X i)) ∧
      (pool X).card < (sources v X).card ∧
      (pool X).card < n := by sorry
end LittleCharity.EFX
