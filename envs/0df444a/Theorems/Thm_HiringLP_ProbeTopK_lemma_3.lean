-- Prove2me | Theorems.Thm_HiringLP_ProbeTopK_lemma_3
-- name    : HiringLP.ProbeTopK.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:44:21.618088+00:00
-- url     : https://prove2.me/theorems/e03cee77-adda-488d-ab7d-b45e9f762b87
-- title:
--   Lemma 3 — R_ALGptk(I) = Σ_i v_i E(1{N_{i−1} < k} Z_i)
-- statement:
--   Let $I$ be a valid ProbeTop-k instance, $(x, y)$ a basic feasible solution of $\mathrm{LP}_{ptk}(I)$, and fix any interview order. Let $R_{ALG_{ptk}}(I)$ be the expected reward of ALGptk run on $(x,y)$ with that order: the interview set $S$ is drawn from DR, the interviewed applicants are processed in order, and applicant $i$ with realised value $r_j$ is hired with probability $x_{ij}/(y_i q_{ij})$ if a position is still open; the reward is the sum of the realised values of the hired applicants.
--
--   Let $Y_i = \mathbf 1\{i \in S\}$, let $P_1, \dots, P_n$ be independent Bernoulli($p_i$) indicators independent of $S$, let $Z_i = Y_i P_i$, and let $N_{i-1}$ be the number of applicants $\ell$ before $i$ in the order with $Z_\ell = 1$. Then
--
--   $$
--   R_{ALG_{ptk}}(I) = \sum_{i=1}^n v_i\, \mathbb{E}\big(\mathbf 1\{N_{i-1} < k\}\, Z_i\big).
--   $$
--
--   The identity replaces the random realised value by the deterministic $v_i$ and the value-dependent hiring coin by an independent indicator of mean $p_i$; it is the bridge from the algorithm to weighted rank functions of the $k$-uniform matroid.
--
--   **Formalization Note.** The paper states the identity for the order of decreasing $v_i$; it does not use the order, so it is stated for every order. Here $p_i, v_i$ follow (4) with footnote 2's zero conventions.
-- source:
--   Epstein, Ma, Selection and Ordering Policies for Hiring Pipelines via Linear Programming, arXiv:2210.04059v3, p. 18, Lemma 3

import Mathlib
import Definitions.Def_HiringLP_ProbeTopK_Model

namespace HiringLP.ProbeTopK

theorem lemma_3 {n J : ℕ} (I : Instance n J) (hI : I.Valid)
    (x : Fin n → Fin J → ℝ) (y : Fin n → ℝ)
    (hext : (x, y) ∈ Set.extremePoints ℝ (feasibleSet I)) (ord : Equiv.Perm (Fin n)) :
    algReward I x y ord = cutValue I x y ord (DR y) := by sorry

end HiringLP.ProbeTopK
