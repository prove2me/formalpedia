-- Prove2me | Theorems.Thm_HighDimStat_MatrixRank_prop10_6_nuclear_norm_oracle_inequality
-- name    : HighDimStat.MatrixRank.prop10_6_nuclear_norm_oracle_inequality
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T23:19:13.373977+00:00
-- url     : https://prove2.me/theorems/b41ae2fe-3141-4985-9a17-10cafd88f267
-- title:
--   The nuclear-norm oracle inequality for matrix regression (Proposition 10.6, goal)
-- statement:
--   **Proposition 10.6.** The chapter's title deterministic result: a direct specialization of
--   chunk `09-decomposability`'s Theorem 9.19 to the nuclear norm, giving an explicit
--   Frobenius-error oracle inequality for low-rank matrix regression.
--
--   Suppose the observation operator $\mathcal X_n$ satisfies the restricted strong convexity
--   condition (10.17) with curvature parameter $\kappa>0$ and tolerance constant $c_0\ge 0$.
--   Then, conditioned on the good event $\mathcal G(\lambda_n) = \{\|\!|\frac1n\sum_{i=1}^n
--   w_iX_i|\!\|_2\le\lambda_n/2\}$, any optimal solution $\hat\Theta$ of nuclear-norm-regularized
--   least squares (10.16) satisfies
--
--   $$
--   \|\!|\hat\Theta-\Theta^*|\!\|_F^2 \le \frac{9}{2}\frac{\lambda_n^2}{\kappa^2}r +
--   \frac{1}{\kappa}\left\{2\lambda_n\sum_{j=r+1}^{d'}\sigma_j(\Theta^*) +
--   \frac{32c_0(d_1+d_2)}{n}\left(\sum_{j=r+1}^{d'}\sigma_j(\Theta^*)\right)^2\right\},
--   $$
--
--   valid for any target rank $r\in\{1,\dots,d'\}$ such that $r\le\kappa n/(128c_0(d_1+d_2))$.
--
--   **Formalization Note** As `BRIEF.md`'s own pitfall names, this is restated *locally* in
--   `HighDimStat.MatrixRank`, never importing chunk `09-decomposability`'s draft — every object
--   (`RSCNuclear`, `opNorm`, `nuclearNorm`, `IsNuclearNormLSSolution`) is its own definition in
--   this mission's `Core` file, instantiated directly for the nuclear norm and Frobenius norm
--   rather than inherited abstractly. `hc0 : 0 ≤ c0` and `hlam : 0 < lamN` are added, matching
--   this chapter's own running convention (RSC "tolerance constants" are always nonnegative
--   throughout the book) and chunk `09`'s analogous `λn>0` convention (see
--   `MODERATION_NOTES.md`).
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 319 (PDF p. 339), Proposition 10.6, Eq. (10.18)

import Mathlib
import Definitions.Def_HighDimStat_MatrixRank_Core

namespace HighDimStat.MatrixRank

/-- Proposition 10.6 (p. 319): suppose the observation operator `Xn` satisfies the restricted
strong convexity condition (10.17) with parameter `κ > 0`. Then, conditioned on the good
event `G(λn) = {|||(1/n)Σwᵢ Xᵢ|||₂ ≤ λn/2}`, any optimal solution to nuclear-norm-regularized
least squares (10.16) satisfies the stated Frobenius-error bound, for any target rank
`r ∈ {1,...,d'}` with `r ≤ κn/(128 c0(d1+d2))`. -/
theorem prop10_6_nuclear_norm_oracle_inequality {d1 d2 n : ℕ}
    (Xs : Fin n → Matrix (Fin d1) (Fin d2) ℝ) (w : Fin n → ℝ)
    (Θstar Θhat : Matrix (Fin d1) (Fin d2) ℝ) (κ c0 lamN : ℝ) (r : ℕ)
    (hκ : 0 < κ) (hc0 : 0 ≤ c0) (hlam : 0 < lamN)
    (hRSC : RSCNuclear Xs κ c0)
    (hG : opNorm ((1 / (n : ℝ)) • observationOpAdjoint Xs w) ≤ lamN / 2)
    (hsol : IsNuclearNormLSSolution Xs (fun i => traceInner (Xs i) Θstar + w i) lamN Θhat)
    (hr1 : 1 ≤ r) (hr2 : r ≤ min d1 d2)
    (hr3 : (r : ℝ) ≤ κ * n / (128 * c0 * ((d1 : ℝ) + d2))) :
    (frobeniusNorm (Θhat - Θstar)) ^ 2 ≤
      9 / 2 * (lamN ^ 2 / κ ^ 2) * r +
        1 / κ * (2 * lamN * tailSingularSum Θstar r +
          32 * c0 * ((d1 : ℝ) + d2) / n * (tailSingularSum Θstar r) ^ 2) := by sorry

end HighDimStat.MatrixRank
