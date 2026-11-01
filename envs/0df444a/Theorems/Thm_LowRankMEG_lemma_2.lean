-- Prove2me | Theorems.Thm_LowRankMEG_lemma_2
-- name    : LowRankMEG.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:51:40.308622+00:00
-- url     : https://prove2.me/theorems/3ee95d6c-7492-4060-ba99-697c42a2747f
-- title:
--   Lemma 2 — the error of one low-rank step
-- statement:
--   Let $X\in\mathcal S_n$, $X\succ0$, let $D$ be symmetric, $\eta>0$, $1\le r<n$, and let $X^*$ be a point of $\mathcal S_n$. Let $Y=\exp(\log(X)-\eta D)$, let $Z_+$ be the exact update and $X_+$ the corresponding low-rank update with $\varepsilon\in(0,3/4]$. Then
--   $$
--   \max\{B(X^*,X_+)-B(X^*,Z_+),\ B(Z_+,X_+)\}\le\max\Bigl\{2\varepsilon,\ \log\frac{(n-r)\lambda_{r+1}(Y)}{\varepsilon\sum_{i=1}^n\lambda_i(Y)}\Bigr\}.
--   $$
--   The error of the low-rank step is thus controlled by one eigenvalue ratio of $Y$. This is the quantity that strict complementarity bounds.
--
--   Differences from the source:
--   - generalization: Y built from ∇f(X) or an unbiased estimator ∇̂ → D any symmetric matrix; reason: (6) and (7) are the cases D = ∇f(X) and D = ∇̂ ∈ 𝕊ⁿ, and the lemma uses nothing else about them
--   - generalization: X* an optimal solution → X* any point of 𝒮_n; reason: an optimal solution is such a point, and optimality plays no role
--   - reading: r and η are not bound in the statement → 1 ≤ r < n and 0 < η; reason: Algorithm 2 and Definition 2
--   - encoding: λ_i with 1-based index → lam X i, with value 0 outside 1 ≤ i ≤ n; reason: every index used is in range under the hypotheses
-- source:
--   Garber & Kaplan, On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for Low-Rank Matrix Optimization, arXiv:2012.10469v2, Lemma 2, p.13

import Mathlib
import Definitions.Def_PSDPolyApprox_densityMatrices
import Definitions.Def_LowRankMEG_bregman
import Definitions.Def_LowRankMEG_lam
import Definitions.Def_LowRankMEG_mlog
import Definitions.Def_LowRankMEG_mexp
import Definitions.Def_LowRankMEG_megStep
import Definitions.Def_LowRankMEG_IsLowRankUpdate

namespace LowRankMEG

/-- **Lemma 2**: for `X ∈ 𝒮_n`, `X ≻ 0`, the exact update `Z₊`, the low-rank update `X₊` and `ε ∈ (0, 3/4]`,
`max{B(X*, X₊) − B(X*, Z₊), B(Z₊, X₊)} ≤ max{2ε, log((n − r)λ_{r+1}(Y)/(ε ∑_{i=1}^n λ_i(Y)))}`.
Garber & Kaplan, *On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for
Low-Rank Matrix Optimization*, arXiv:2012.10469v2, Lemma 2, p.13.

**Formalization Note.** `D` is any symmetric matrix, which covers `∇f(X)` of (6) and `∇̂` of (7): the lemma uses
nothing else about them. `Xs` is any point of `𝒮_n`, in particular an optimum. `1 ≤ r < n` is Algorithm 2's
range of `r`; `η > 0` is from Definition 2. -/
theorem lemma_2 {n r : ℕ} {X D Xs Xp : Matrix (Fin n) (Fin n) ℝ} {η ε : ℝ}
    (hX : X ∈ PSDPolyApprox.densityMatrices n) (hXpd : X.PosDef) (hD : D.IsSymm) (hXs : Xs ∈ PSDPolyApprox.densityMatrices n)
    (hr : 1 ≤ r) (hrn : r < n) (hη : 0 < η) (hε : ε ∈ Set.Ioc (0 : ℝ) (3 / 4))
    (hXp : IsLowRankUpdate X D η ε r Xp) :
    let Y := mexp (mlog X - η • D)
    let Zp := megStep X D η
    max (bregman Xs Xp - bregman Xs Zp) (bregman Zp Xp) ≤
      max (2 * ε)
        (Real.log (((n : ℝ) - r) * lam Y (r + 1) / (ε * ∑ i ∈ Finset.Icc 1 n, lam Y i))) := by sorry

end LowRankMEG
