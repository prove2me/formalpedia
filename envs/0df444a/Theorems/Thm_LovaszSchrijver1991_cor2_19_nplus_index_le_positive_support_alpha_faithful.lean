-- Prove2me | Theorems.Thm_LovaszSchrijver1991_cor2_19_nplus_index_le_positive_support_alpha_faithful
-- name    : LovaszSchrijver1991.cor2_19_nplus_index_le_positive_support_alpha_faithful
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-23T01:35:16.340905+00:00
-- url     : https://prove2.me/theorems/2b4e1f57-4ecc-420c-b582-98263afb8b26
-- title:
--   Corollary 2.19 — $N_+$-index at most the stability number of the positive support
-- statement:
--   Let $G = (V, E)$ be a finite graph with no isolated nodes, let $\mathrm{STAB}(G)$ be its stable set polytope and let $N_+^r(G)$ be the $r$-th iterate of the Lovász–Schrijver semidefinite operator $N_+$ applied to the fractional stable set cone $\mathrm{FR}(G)$, dehomogenized at $x_0 = 1$ (so $N_+^0(G) = \mathrm{FRAC}(G)$). Let $a \in \mathbb R^V$, $b \in \mathbb R$ be such that $a^{\mathsf T}x \le b$ is valid for $\mathrm{STAB}(G)$, and let $P = \{i \in V : a_i > 0\}$. If every stable set of $G$ contained in $P$ has at most $r$ nodes, i.e. $\alpha(G[P]) \le r$, then
--
--   $$a^{\mathsf T}x \le b \quad \text{for every } x \in N_+^r(G),$$
--
--   that is, the inequality has $N_+$-index at most $r$.
--
--   This is the first sentence of Corollary 2.19 of Lovász and Schrijver (1991). It generalizes the index bound of Corollary 2.15, which is the goal of the mission.
--
--   **Formalization Note** "Independence number $r$" is written as "every stable set inside the positive support has at most $r$ nodes"; since $N_+^{r}(G) \subseteq N_+^{r'}(G)$ for $r \ge r'$, this is equivalent. The second sentence ("index at most $b$") is not included.
-- source:
--   Lovász and Schrijver, Cones of matrices and set-functions and 0–1 optimization, SIAM J. Optim. 1(2) (1991), doi:10.1137/0801013, p. 183, Corollary 2.19

import Mathlib
import Definitions.Def_LovaszSchrijver_NPlus_StableSet
open LovaszSchrijver.NPlus

theorem LovaszSchrijver1991.cor2_19_nplus_index_le_positive_support_alpha_faithful
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : ∀ v, ∃ w, G.Adj v w)
    (a : V → ℝ) (b : ℝ) (r : ℕ)
    (hvalid : Valid (STAB G) a b)
    (hα : ∀ A : Finset V, G.IsIndepSet (A : Set V) → (A : Set V) ⊆ {i | 0 < a i} → A.card ≤ r) :
    Valid (NplusG r G) a b := by sorry
