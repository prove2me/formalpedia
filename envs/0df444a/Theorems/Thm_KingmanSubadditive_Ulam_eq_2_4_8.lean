-- Prove2me | Theorems.Thm_KingmanSubadditive_Ulam_eq_2_4_8
-- name    : KingmanSubadditive.Ulam.eq_2_4_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:46:17.65827+00:00
-- url     : https://prove2.me/theorems/69e80b40-5d7a-41cc-a0d1-674a2d2a1c91
-- title:
--   (2.4.8) — if 0 < α < β and 2α + (β−α)log(β−α) − α log α − β log β < 0, then P{l(π) ≥ βn^½} → 0
-- statement:
--   Let $0<\alpha<b<\infty$ satisfy
--   $$2\alpha+(b-\alpha)\log(b-\alpha)-\alpha\log\alpha-b\log b<0. \tag{2.4.8}$$
--   Then, for $\pi$ uniformly distributed over $\mathcal S_n$,
--   $$P\{l(\pi)\ge b\,n^{1/2}\}\to0\qquad(n\to\infty).$$
--
--   In the paper this follows from (2.4.7) and Stirling's formula with $k\sim\alpha n^{1/2}$ and $r\sim b\, n^{1/2}$; it shows that the constant $c$ of Theorem 7 satisfies $c\le b$ for every such $b$.
--
--   **Formalization Note** The paper calls the parameter $\beta$; it is $b$ here because $\beta$ is also the constant $\delta^{1/2}+\delta^{-1/2}$ of Theorem 8.
-- source:
--   Kingman, Subadditive ergodic theory, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798, p. 896, §2.4, proof of Theorem 8, (2.4.8)

import Mathlib
import Definitions.Def_KingmanSubadditive_Ulam_Permutations

open Filter Topology

namespace KingmanSubadditive.Ulam

/-- **The Stirling step (2.4.8)** (Kingman, *Subadditive ergodic theory*, Ann. Probab.
1(6):883–899 (1973), §2.4, proof of Theorem 8, p. 896). Let `0 < α < b < ∞`. If
`2α + (b − α) log (b − α) − α log α − b log b < 0`, then `P{l(π) ≥ b n^½} → 0` as `n → ∞`, where
`π` is uniform on `𝒮_n`.

**Formalization Note** The paper calls the free parameter `β`; it is `b` here because `β` is also
the constant of Theorem 8. The paper obtains this from (2.4.7) with `k ~ α n^½`, `r ~ β n^½`; the
statement is the conclusion, for every admissible pair `(α, b)`. -/
theorem eq_2_4_8 (α b : ℝ) (hα : 0 < α) (hαb : α < b) (h : stirlingExponent α b < 0) :
    Tendsto (fun n : ℕ => unifProb n (fun σ => b * Real.sqrt n ≤ (lis σ : ℝ))) atTop (𝓝 0) := by sorry

end KingmanSubadditive.Ulam
