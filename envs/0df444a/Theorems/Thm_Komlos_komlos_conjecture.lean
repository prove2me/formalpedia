-- Prove2me | Theorems.Thm_Komlos_komlos_conjecture
-- name    : Komlos.komlos_conjecture
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-03T20:50:28.939907+00:00
-- url     : https://prove2.me/theorems/22be6be2-94e7-47b4-86c2-d6c868541e6c
-- title:
--   The Komlós conjecture
-- statement:
--   **The Komlós conjecture.** There is a universal constant $K$ such that any finite family of vectors $v_1, \dots, v_n \in \mathbb{R}^m$ of Euclidean norm at most $1$ admits signs $\varepsilon_i \in \{\pm 1\}$ with
--   $$\Big\lVert \sum_{i=1}^n \varepsilon_i v_i \Big\rVert_\infty \le K,$$
--   independently of $n$ and $m$. The conjecture implies the Beck--Fiala conjecture ($O(\sqrt{t})$ discrepancy for degree-$t$ set systems). The best upper bound is $\tilde{O}((\log n)^{1/4})$ (Bansal--Jiang 2025, after Banaszczyk's $O(\sqrt{\log n})$ of 1998); the best lower bound on $K$ is $1 + \sqrt{2}$ (Kunisky 2023). Open since the 1980s.
-- source:
--   Attributed to J. Komlos (1980s, unpublished); statement as in Nikolov's lecture notes on discrepancy theory and Kunisky, SIAM J. Discrete Math. 37 (2023), https://arxiv.org/abs/2111.02974

import Mathlib
import Definitions.Def_Komlos_model

namespace Komlos

theorem komlos_conjecture : ∃ K : ℝ, KomlosBound K := by sorry

end Komlos
