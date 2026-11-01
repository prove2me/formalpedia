-- Prove2me | Theorems.Thm_LowRankMEG_theorem_2
-- name    : LowRankMEG.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:51:37.341594+00:00
-- url     : https://prove2.me/theorems/14e1b4e2-d3c7-4d55-9e4a-2d707507dc94
-- title:
--   Theorem 2 (corrected: minimum up to $T+1$, error sum to $T$) — convergence of inexact MEG
-- statement:
--   Let $\{X_t\}_{t\ge1}$ be a sequence of points in $\mathcal S_n\cap\mathbb S^n_{++}$. Let $Z_1=X_1$, and for $t\ge1$ let $Z_{t+1}$ be the exact update (6) of $X_t$ with step size $\eta\le1/\beta$. Let $X^*$ be an optimal solution. Then for any $T\ge1$,
--   $$
--   \min_{1\le t\le T+1}f(X_t)-f(X^*)\le\frac1{\eta T}B(X^*,X_1)+\frac1{\eta T}\sum_{t=1}^{T-1}\bigl(B(X^*,X_{t+1})-B(X^*,Z_{t+1})\bigr)+\frac2T\sum_{t=1}^{T}\|\nabla f(X_{t+1})\|_2\sqrt{B(Z_{t+1},X_{t+1})}.
--   $$
--   The first term is the standard rate of mirror descent, and the others account for the inexact updates. The sequence is arbitrary, so the theorem applies to any approximation of the exact method.
--
--   Differences from the source:
--   - correction: min over 1 ≤ t ≤ T and the last sum to T − 1 → min over 1 ≤ t ≤ T + 1 and the last sum to T; reason: the printed bound is false: at T = 1 with n = 2, f(X) = X₂₂, β = 1/2, η = 2, X₁ = I/2 the sums are empty and it claims 1/2 ≤ (log 2)/2; the proof bounds f(X_{t+1}) for t ≥ 1 only, and the first sum stays at T − 1 because B(X*, Z_{T+1}) ≥ 0
--   - reading: X* is not bound in the statement → X* any optimal solution; reason: it is the 𝒳* of p.3, and the proof uses optimality
--   - encoding: the gradient ∇f → a map grad tied to f by HasFDerivAt at symmetric matrices (Setting.hasGrad); reason: Lean needs ∇f as data; same instances
--   - encoding: step size up to 1/β → 0 < β; reason: excludes an undefined case only
--   - encoding: a minimum over a finite range of t → ∃ t in that range; reason: the two are equivalent on a finite nonempty range
--   - encoding: a step size η ≤ 1/β → 0 < η; reason: step sizes are positive, p.6
-- source:
--   Garber & Kaplan, On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for Low-Rank Matrix Optimization, arXiv:2012.10469v2, Theorem 2, p.10, corrected

import Mathlib
import Definitions.Def_LowRankMEG_Setting
import Definitions.Def_LowRankMEG_IsOptimal
import Definitions.Def_PSDPolyApprox_densityMatrices
import Definitions.Def_LowRankMEG_bregman
import Definitions.Def_LowRankMEG_megStep
import Definitions.Def_WainwrightHDS_NucNorm_opNorm2

namespace LowRankMEG

/-- **Theorem 2, convergence with deterministic updates (corrected: minimum up to `T + 1`, error sum to
`T`).** For any sequence `X_t` in `𝒮_n ∩ 𝕊ⁿ₊₊`, `Z₁ = X₁` and `Z_{t+1}` the exact update (6) of `X_t`,
`η ≤ 1/β`, `T ≥ 1`:
`min_{1≤t≤T+1} f(X_t) − f(X*) ≤ (1/(ηT))B(X*, X₁) + (1/(ηT))∑_{t=1}^{T−1}(B(X*, X_{t+1}) − B(X*, Z_{t+1}))
  + (2/T)∑_{t=1}^{T} ‖∇f(X_{t+1})‖₂ √B(Z_{t+1}, X_{t+1})`.
Garber & Kaplan, *On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for
Low-Rank Matrix Optimization*, arXiv:2012.10469v2, Theorem 2, p.10, corrected.

**Formalization Note.** The page has `min_{1≤t≤T}` and its last sum to `T − 1`. That is false: at `T = 1`
with `n = 2`, `f(X) = X₂₂`, `β = 1/2`, `η = 2`, `X₁ = I/2` it claims `1/2 ≤ (log 2)/2`. The proof on pp.10–11 bounds
`f(X_{t+1})` for `t ≥ 1`, so `f(X₁)` is not reached in `T` steps. The minimum is `∃ t` in a finite nonempty
range. `0 < β` because of `1/β`. -/
theorem theorem_2 {n : ℕ} {f : Matrix (Fin n) (Fin n) ℝ → ℝ}
    {grad : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ} {β : ℝ}
    (hS : Setting f grad β) (hβ : 0 < β)
    {Xs : Matrix (Fin n) (Fin n) ℝ} (hopt : IsOptimal f Xs)
    {X Z : ℕ → Matrix (Fin n) (Fin n) ℝ} {η : ℝ} (hη : 0 < η) (hηβ : η ≤ 1 / β)
    (hX : ∀ t, 1 ≤ t → X t ∈ PSDPolyApprox.densityMatrices n) (hXpd : ∀ t, 1 ≤ t → (X t).PosDef)
    (hZ1 : Z 1 = X 1) (hZ : ∀ t, 1 ≤ t → Z (t + 1) = megStep (X t) (grad (X t)) η)
    {T : ℕ} (hT : 1 ≤ T) :
    ∃ t ∈ Finset.Icc 1 (T + 1),
      f (X t) - f Xs ≤
        1 / (η * T) * bregman Xs (X 1)
          + 1 / (η * T) * ∑ s ∈ Finset.Icc 1 (T - 1),
              (bregman Xs (X (s + 1)) - bregman Xs (Z (s + 1)))
          + 2 / (T : ℝ) * ∑ s ∈ Finset.Icc 1 T,
              WainwrightHDS.NucNorm.opNorm2 (grad (X (s + 1))) * Real.sqrt (bregman (Z (s + 1)) (X (s + 1))) := by sorry

end LowRankMEG
