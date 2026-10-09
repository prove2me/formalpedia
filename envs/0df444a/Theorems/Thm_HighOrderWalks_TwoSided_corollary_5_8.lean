-- Prove2me | Theorems.Thm_HighOrderWalks_TwoSided_corollary_5_8
-- name    : HighOrderWalks.TwoSided.corollary_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:41:00.500984+00:00
-- url     : https://prove2.me/theorems/84319c74-f989-4f46-b483-2b36017b8850
-- title:
--   Corollary 5.8, p. 22 — ‖M⁺_k P_{U^j_k}φ − ((k+1−j)/(k+2))P_{U^j_k}φ‖ ≤ (ε_k/(k+2))‖P_{U^j_k}φ‖
-- statement:
--   Let $X$ be a pure $n$-dimensional weighted simplicial complex that is a two-sided $\lambda$-local spectral expander, with the constants $\varepsilon_k$ of Theorem 5.6, and assume $\varepsilon_k\le\dfrac{1}{2\big(1+2(k+1)\sqrt{k+1}\big)}$ for all $0\le k\le n-2$. Then for every $0\le k\le n-1$, every $0\le j\le k$ and every $\phi\in C^k_0(X)$,
--   $$\Big\|M^+_kP_{U^j_k}\phi-\frac{k+1-j}{k+2}\,P_{U^j_k}\phi\Big\|\le\frac{\varepsilon_k}{k+2}\,\big\|P_{U^j_k}\phi\big\| ,$$
--   where $M^+_k$ is the upper random walk on $k$-faces and $P_{U^j_k}$ the weighted orthogonal projection onto $U^j_k$.
--
--   This is Theorem 5.6 rescaled by $d^*_kd_k=(k+2)M^+_k$ (Corollary 3.7): on each $U^j_k$ the walk $M^+_k$ is close to multiplication by $\frac{k+1-j}{k+2}$.
--
--   **Formalization Note.** As in Theorem 5.6: $k$ is quantified in the conclusion, $P_{U^j_k}\phi$ is any $u$ with `IsWProj X m (k + 1) (Usp X m k j) φ u`, and `eps lam k` is $\varepsilon_k$.
-- source:
--   Kaufman–Oppenheim, High Order Random Walks: Beyond Spectral Gap, arXiv:1707.02799v3, p. 22, Corollary 5.8

import Mathlib
import Definitions.Def_HighOrderWalks_TwoSided_Setting
import Definitions.Def_HighOrderWalks_TwoSided_Subspaces

namespace HighOrderWalks.TwoSided

/-- Corollary 5.8, p. 22: under the hypotheses of Theorem 5.6, for every `0 ≤ k ≤ n - 1`,
`0 ≤ j ≤ k` and `φ ∈ C^k_0(X)`, with `u = P_{U^j_k} φ`,
`‖M⁺_k u - ((k + 1 - j)/(k + 2)) u‖ ≤ (ε_k/(k + 2)) ‖u‖`. -/
theorem corollary_5_8 {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (n : ℕ)
    (hX : HighOrderWalks.OneSided.IsPureComplex X n) (m : Finset V → ℝ) (hm : HighOrderWalks.OneSided.IsWeight X n m)
    (lam : ℝ) (hexp : TwoSidedLSE X m n lam)
    (hsmall : ∀ k : ℕ, k + 2 ≤ n →
      eps lam k ≤ 1 / (2 * (1 + 2 * ((k : ℝ) + 1) * Real.sqrt ((k : ℝ) + 1)))) :
    ∀ k : ℕ, k + 1 ≤ n → ∀ j ≤ k, ∀ φ ∈ C0 X m (k + 1), ∀ u : Finset V → ℝ,
      IsWProj X m (k + 1) (Usp X m k j) φ u →
        HighOrderWalks.OneSided.nrm X m (k + 1) (HighOrderWalks.OneSided.upperWalk X m u - (((k : ℝ) + 1 - (j : ℝ)) / ((k : ℝ) + 2)) • u) ≤
          eps lam k / ((k : ℝ) + 2) * HighOrderWalks.OneSided.nrm X m (k + 1) u := by sorry

end HighOrderWalks.TwoSided
