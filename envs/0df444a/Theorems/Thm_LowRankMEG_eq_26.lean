-- Prove2me | Theorems.Thm_LowRankMEG_eq_26
-- name    : LowRankMEG.eq_26
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:51:02.21245+00:00
-- url     : https://prove2.me/theorems/3cccd36f-94f8-48cf-bca9-73e4014abfb8
-- title:
--   (26) — the bound on $\log\lambda_{r^*+1}(Y)$
-- statement:
--   Let $X^*$ be optimal of rank $r^*<n$, let $X\in\mathcal S_n$, $X\succ0$, let $D$ be symmetric with $\|D-\nabla f(X)\|_2\le\xi$, let $\eta>0$, and let $Y=\exp(\log(X)-\eta D)$. Then
--   $$
--   \log\lambda_{r^*+1}(Y)\le\log\lambda_{r^*+1}(X)-\eta\lambda_{n-r^*}(\nabla f(X^*))+\eta\frac{2\sqrt{2r^*}\|X-X^*\|_*}{\lambda_{r^*}(X^*)}\|\nabla f(X^*)\|_2+\eta\xi+\eta\beta\|X-X^*\|_*.
--   $$
--   The display is derived in the proof of Lemma 3, and Lemma 6 uses it again with $\xi=0$. It shows how fast an exact step reduces the eigenvalue $\lambda_{r^*+1}$.
--
--   Differences from the source:
--   - encoding: ∇̃ ∈ 𝕊ⁿ of Lemma 3 → D symmetric; reason: notation
--   - generalization: stated inside Lemma 3, under Assumption 1 and (19) and with λ_{r*+1}(X) bounded → only X* optimal, r* < n, X ≻ 0 in 𝒮_n and ‖D − ∇f(X)‖₂ ≤ ξ; reason: the derivation on pp.15–16 uses none of the others, and Lemma 6 (p.21) cites (26) outside Lemma 3
--   - encoding: the gradient ∇f → a map grad tied to f by HasFDerivAt at symmetric matrices (Setting.hasGrad); reason: Lean needs ∇f as data; same instances
--   - encoding: λ_i with 1-based index → lam X i, with value 0 outside 1 ≤ i ≤ n; reason: every index used is in range under the hypotheses
--   - encoding: ξ ≥ 0 → no sign condition on ξ; reason: it follows from ‖D − ∇f(X)‖₂ ≤ ξ
-- source:
--   Garber & Kaplan, On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for Low-Rank Matrix Optimization, arXiv:2012.10469v2, Eq. (26), p.16

import Mathlib
import Definitions.Def_LowRankMEG_Setting
import Definitions.Def_LowRankMEG_IsOptimal
import Definitions.Def_PSDPolyApprox_densityMatrices
import Definitions.Def_LowRankMEG_lam
import Definitions.Def_LowRankMEG_mlog
import Definitions.Def_LowRankMEG_mexp
import Definitions.Def_WainwrightHDS_NucNorm_nucNorm
import Definitions.Def_WainwrightHDS_NucNorm_opNorm2

namespace LowRankMEG

/-- **Eq. (26)**: with `Y = exp(log(X) − ηD)`, `‖D − ∇f(X)‖₂ ≤ ξ`,
`log λ_{r*+1}(Y) ≤ log λ_{r*+1}(X) − ηλ_{n−r*}(∇f(X*)) + η(2√(2r*)‖X − X*‖_*/λ_{r*}(X*))‖∇f(X*)‖₂ + ηξ + ηβ‖X − X*‖_*`.
Garber & Kaplan, *On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for
Low-Rank Matrix Optimization*, arXiv:2012.10469v2, Eq. (26), p.16, in the proof of Lemma 3.

**Formalization Note.** Stated in the generality the paper uses it: Lemma 3 at `D = ∇̃`, and Lemma 6 at
`D = ∇f(X_t)`, `ξ = 0` ("We have seen in (26) with ξ = 0", p.21). It uses no strict complementarity, no ball
around `X*`, and no bound on `λ_{r*+1}(X)`. `Xs.rank < n` makes `n − r*` exact and `r* + 1 ≤ n`. -/
theorem eq_26 {n : ℕ} {f : Matrix (Fin n) (Fin n) ℝ → ℝ}
    {grad : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ} {β : ℝ}
    (hS : Setting f grad β)
    {Xs X D : Matrix (Fin n) (Fin n) ℝ} (hopt : IsOptimal f Xs) (hrs : Xs.rank < n)
    (hX : X ∈ PSDPolyApprox.densityMatrices n) (hXpd : X.PosDef) (hD : D.IsSymm) {ξ η : ℝ}
    (hDξ : WainwrightHDS.NucNorm.opNorm2 (D - grad X) ≤ ξ) (hη : 0 < η) :
    Real.log (lam (mexp (mlog X - η • D)) (Xs.rank + 1)) ≤
      Real.log (lam X (Xs.rank + 1)) - η * lam (grad Xs) (n - Xs.rank)
        + η * (2 * Real.sqrt (2 * (Xs.rank : ℝ)) * WainwrightHDS.NucNorm.nucNorm (X - Xs) / lam Xs Xs.rank)
            * WainwrightHDS.NucNorm.opNorm2 (grad Xs)
        + η * ξ + η * β * WainwrightHDS.NucNorm.nucNorm (X - Xs) := by sorry

end LowRankMEG
