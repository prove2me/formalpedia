-- Prove2me | Theorems.Thm_LovaszSchrijver_Defect_one_div_add_two_mem_NG
-- name    : LovaszSchrijver.Defect.one_div_add_two_mem_NG
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T15:56:02.439512+00:00
-- url     : https://prove2.me/theorems/187baa97-81b0-4bdf-bf53-3c6f332ba556
-- title:
--   Lemma 2.7 — (1/(k+2))𝟙 lies in Nᵏ(G)
-- statement:
--   Let $G = (V,E)$ be a finite graph with no isolated nodes and let $\mathbb 1 \in \mathbb R^V$ be the all-ones vector. Then for every $k \ge 0$,
--   $$\frac{1}{k+2}\,\mathbb 1 \in N^k(G).$$
--
--   This point shows that $k$ rounds of $N$ cannot cut off the uniform vector $\frac1{k+2}\mathbb 1$; it gives the lower bound in Theorem 2.13 and in Corollary 2.8.
--
--   **Formalization Note** $k + 2$ is computed in $\mathbb R$. For $k = 0$ the statement is $\tfrac12\mathbb 1 \in \mathrm{FRAC}(G)$.
-- source:
--   Lovász and Schrijver, Cones of matrices and set-functions and 0–1 optimization, SIAM J. Optim. 1(2) (1991), p. 180, Lemma 2.7

import Mathlib
import Definitions.Def_LovaszSchrijver_Defect_Index

namespace LovaszSchrijver.Defect

theorem one_div_add_two_mem_NG {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : ∀ v, ∃ w, G.Adj v w) (k : ℕ) :
    (fun _ : V => 1 / ((k : ℝ) + 2)) ∈ NG k G := by sorry

end LovaszSchrijver.Defect
