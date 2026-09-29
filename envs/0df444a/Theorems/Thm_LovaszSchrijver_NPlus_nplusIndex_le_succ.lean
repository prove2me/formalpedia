-- Prove2me | Theorems.Thm_LovaszSchrijver_NPlus_nplusIndex_le_succ
-- name    : LovaszSchrijver.NPlus.nplusIndex_le_succ
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:59:55.433377+00:00
-- url     : https://prove2.me/theorems/f5156723-6a11-42ed-a3de-e02b83e69357
-- title:
--   Lemma 2.14 — if every positive contraction has N₊-index ≤ r, the inequality has N₊-index ≤ r + 1
-- statement:
--   Let $G = (V,E)$ be a finite graph with no isolated nodes, and let $a^{\mathsf T}x \le b$ be an inequality valid for $\mathrm{STAB}(G)$ (no sign condition on $a$). Suppose that for every node $v$ with $a_v > 0$ the contraction of $v$, i.e. the inequality $a'^{\mathsf T}x \le b - a_v$ where $a'$ is $a$ with the coefficients of $v$ and of its neighbours set to $0$, is valid for $N_+^r(G)$. Then
--   $$a^{\mathsf T}x \le b \quad \text{for all } x \in N_+^{r+1}(G).$$
--
--   That is, if all these contractions have $N_+$-index at most $r$, then $a^{\mathsf T}x \le b$ has $N_+$-index at most $r+1$ (paper, p. 183). It turns a local property of the constraint (what remains after contracting a node) into a bound on the number of $N_+$ rounds.
--
--   **Formalization Note** "$N_+$-index at most $r$" is stated as validity for $N_+^r(G)$; the two are equivalent because the relaxations $N_+^i(G)$ decrease in $i$. As on the page, no sign condition is placed on $a$. The contraction is written on the same graph $G$ (see the definition file).
-- source:
--   Lovász and Schrijver, Cones of matrices and set-functions and 0–1 optimization, SIAM J. Optim. 1(2) (1991), p. 183, Lemma 2.14

import Mathlib
import Definitions.Def_LovaszSchrijver_NPlus_StableSet

namespace LovaszSchrijver.NPlus

theorem nplusIndex_le_succ {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : ∀ v, ∃ w, G.Adj v w)
    (a : V → ℝ) (b : ℝ) (hvalid : Valid (STAB G) a b) (r : ℕ)
    (hcontract : ∀ v, 0 < a v → Valid (NplusG r G) (contractCoeff G a v) (b - a v)) :
    Valid (NplusG (r + 1) G) a b := by sorry

end LovaszSchrijver.NPlus
