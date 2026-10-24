-- Prove2me | Theorems.Thm_HiringLP_ProbeTopK_independent_version_bound
-- name    : HiringLP.ProbeTopK.independent_version_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:44:17.414323+00:00
-- url     : https://prove2.me/theorems/ec77f9dc-7ca1-4df7-a7e2-17e925cf38f5
-- title:
--   App. B.5, p. ec8 — the independent-rounding version of ALGptk earns at least (1 − e^{−k}k^k/k!) LPptk
-- statement:
--   Let $I$ be a valid ProbeTop-k instance and let $(x, y)$ be an optimal solution of $\mathrm{LP}_{ptk}(I)$, so that its objective is $\mathrm{LP}_{ptk}(I)$. Consider the hypothetical algorithm $\mathrm{ALG}'_{ptk}$ that interviews each applicant $i$ independently with probability $y_i$ (instead of using DR), interviews in decreasing order of $v_i$, and otherwise behaves like ALGptk. With $\tilde Y_i$ independent Bernoulli($y_i$), $P_i$ independent Bernoulli($p_i$), $\tilde Z_i = \tilde Y_i P_i$ and $\tilde N_{i-1}$ the number of $\ell$ before $i$ with $\tilde Z_\ell = 1$, its expected reward is $R_{ALG'_{ptk}}(I) = \sum_i v_i\, \mathbb{E}(\tilde Z_i \mathbf 1\{\tilde N_{i-1} < k\})$, and
--
--   $$
--   R_{ALG'_{ptk}}(I) \;\ge\; \Big(1 - \frac{e^{-k}k^k}{k!}\Big)\, \mathrm{LP}_{ptk}(I).
--   $$
--
--   Together with Lemma 4 (and Lemma 3) this gives Theorem 1.
--
--   **Formalization Note.** The page writes the ratio $R_{ALG'_{ptk}}(I)/\mathrm{LP}_{ptk}(I) \ge 1 - e^{-k}k^k/k!$; it is stated multiplicatively. The order is a permutation sorted by $v$ (`SortedBy`), ties in any order. The reward of $\mathrm{ALG}'_{ptk}$ is the quantity of Lemma 3 with independent rounding of $y$ in place of DR.
-- source:
--   Epstein, Ma, Selection and Ordering Policies for Hiring Pipelines via Linear Programming, arXiv:2210.04059v3, p. ec8 (PDF p. 40), App. B.5, fourth display

import Mathlib
import Definitions.Def_HiringLP_ProbeTopK_WeightedRank
import Definitions.Def_HiringLP_ProbeTopK_Model

namespace HiringLP.ProbeTopK

theorem independent_version_bound {n J : ℕ} (I : Instance n J) (hI : I.Valid)
    (x : Fin n → Fin J → ℝ) (y : Fin n → ℝ) (hopt : IsLPOpt I x y)
    (ord : Equiv.Perm (Fin n)) (hord : SortedBy ord (vbar I x)) :
    (1 - Real.exp (-(I.k : ℝ)) * (I.k : ℝ) ^ I.k / (I.k.factorial : ℝ)) * LPobj I x y ≤
      cutValue I x y ord (indepProb y) := by sorry

end HiringLP.ProbeTopK
