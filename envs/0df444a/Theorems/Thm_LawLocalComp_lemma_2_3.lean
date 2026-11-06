-- Prove2me | Theorems.Thm_LawLocalComp_lemma_2_3
-- name    : LawLocalComp.lemma_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:12:30.582853+00:00
-- url     : https://prove2.me/theorems/8c313ba2-d467-47b1-996d-21bf38110dca
-- title:
--   Lemma 2.3 (Call deficits transfer to norms)
-- statement:
--   Let $Y_j$ be a conditional-mean replacement of $X_j$, of mean $\mu_j$, for $j=1,\dots,n$, and let $\theta,\alpha,\beta\ge0$ satisfy
--   $$0\le C_{X_j}(t)-C_{Y_j}(t)\le\theta\,\mathbb E[Y_j\mathbf 1\{Y_j>t\}]+\alpha\mu_j+\beta t\qquad(t\ge0).\tag{6}$$
--   For independent jobs with nonnegative directions of rank at most $q$ and any monotone norm $g$, with $F=\mathbb E g(L)$ and $\tilde F=\mathbb E g(\tilde L)$,
--   $$[1-\alpha q-\beta n(1+\theta)]\,F\le(1+\theta)\,\tilde F,\qquad\tilde F\le F.\tag{7}$$
--
--   This lemma converts the scalar call certificates of the cell constructions into the vector guarantee (1).
--
--   Differences from the source:
--   - generalization: laws of the model (finite nonnegative rational) → arbitrary finite nonnegative real laws; reason: the lemma's proof uses no rationality; specializes to rational laws
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), Lemma 2.3, (6)–(7), p.4

import Mathlib
import Definitions.Def_LawLocalComp_IsCondMean
import Definitions.Def_LawLocalComp_call
import Definitions.Def_LawLocalComp_upperMoment
import Definitions.Def_LawLocalComp_mean
import Definitions.Def_LawLocalComp_IsMonotoneNorm
import Definitions.Def_LawLocalComp_expNorm
import Definitions.Def_LawLocalComp_dirRank

namespace LawLocalComp

/-- **Lemma 2.3 (Call deficits transfer to norms).**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), Lemma 2.3, (6)–(7), p.4.

Let each `Y_j` be a conditional-mean replacement of `X_j`, of mean `µ_j`, and let `θ, α, β ≥ 0` satisfy
`0 ≤ C_{X_j}(t) − C_{Y_j}(t) ≤ θE[Y_j 1{Y_j > t}] + αµ_j + βt` for `t ≥ 0` (6). For `n` independent jobs
with nonnegative directions of rank at most `q` and any monotone norm `g`, with `F = E g(L)` and
`F̃ = E g(L̃)`: `[1 − αq − βn(1 + θ)]F ≤ (1 + θ)F̃` and `F̃ ≤ F` (7). -/
theorem lemma_2_3 {d n : ℕ} (X Y : Fin n → Law) (θ α β : ℝ) (hθ : 0 ≤ θ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hCM : ∀ j, IsCondMean (X j) (Y j))
    (hcert : ∀ j, ∀ t : ℝ, 0 ≤ t → 0 ≤ call (X j) t - call (Y j) t ∧
      call (X j) t - call (Y j) t ≤ θ * upperMoment (Y j) t + α * mean (X j) + β * t)
    (a : Fin n → Fin d → ℝ) (ha : ∀ j, 0 ≤ a j) (q : ℕ) (hq : dirRank a ≤ q)
    (g : (Fin d → ℝ) → ℝ) (hg : IsMonotoneNorm g) :
    (1 - α * q - β * n * (1 + θ)) * expNorm g X a ≤ (1 + θ) * expNorm g Y a ∧
      expNorm g Y a ≤ expNorm g X a := by sorry

end LawLocalComp
