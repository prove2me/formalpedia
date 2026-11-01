-- Prove2me | Theorems.Thm_LowRankMEG_eq_11
-- name    : LowRankMEG.eq_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:51:31.431056+00:00
-- url     : https://prove2.me/theorems/b853d2b5-a927-4870-b537-c5d2d79951c4
-- title:
--   (11) — the three-point inequality for an exact MEG step
-- statement:
--   Let $X_t\in\mathcal S_n$, $X_t\succ0$, let $\eta>0$, and let $Z_{t+1}$ be the exact update (6) of $X_t$. For every $X\in\mathcal S_n$, possibly singular,
--   $$
--   \eta\langle\nabla f(X_t),Z_{t+1}-X\rangle\le\langle\nabla\omega(X_t)-\nabla\omega(Z_{t+1}),Z_{t+1}-X\rangle=B(X,X_t)-B(X,Z_{t+1})-B(Z_{t+1},X_t).
--   $$
--   Here $\omega(X)=\operatorname{Tr}(X\log(X)-X)$ and $\langle A,B\rangle=\operatorname{Tr}(AB)$. This is the basic inequality of mirror descent, and it drives Theorem 2 and Lemma 5.
--
--   Differences from the source:
--   - encoding: the gradient ∇f → a map grad tied to f by HasFDerivAt at symmetric matrices (Setting.hasGrad); reason: Lean needs ∇f as data; same instances
--   - encoding: ∇ω(X) → log(X); reason: ω(X) = Tr(X log(X) − X) has gradient log(X) at X ≻ 0, p.5
-- source:
--   Garber & Kaplan, On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for Low-Rank Matrix Optimization, arXiv:2012.10469v2, Eq. (11), p.10

import Mathlib
import Definitions.Def_LowRankMEG_Setting
import Definitions.Def_PSDPolyApprox_densityMatrices
import Definitions.Def_LowRankMEG_bregman
import Definitions.Def_LowRankMEG_mlog
import Definitions.Def_LowRankMEG_megStep

namespace LowRankMEG

/-- **Eq. (11)**: the three-point inequality of an exact MEG step: for `Z = Z_{t+1}` the update (6) of
`X_t` and every `X ∈ 𝒮_n`,
`η⟨∇f(X_t), Z − X⟩ ≤ ⟨∇ω(X_t) − ∇ω(Z), Z − X⟩ = B(X, X_t) − B(X, Z) − B(Z, X_t)`.
Garber & Kaplan, *On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for
Low-Rank Matrix Optimization*, arXiv:2012.10469v2, Eq. (11), p.10.

**Formalization Note.** `∇ω = log`, since `ω(X) = Tr(X log(X) − X)` on p.5 has gradient `log` at `X ≻ 0`.
`⟨A, B⟩ = Tr(AB)`. Both relations of the chain are stated. -/
theorem eq_11 {n : ℕ} {f : Matrix (Fin n) (Fin n) ℝ → ℝ}
    {grad : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ} {β : ℝ}
    (hS : Setting f grad β)
    {Xt X : Matrix (Fin n) (Fin n) ℝ} {η : ℝ} (hη : 0 < η)
    (hXt : Xt ∈ PSDPolyApprox.densityMatrices n) (hXtpd : Xt.PosDef) (hX : X ∈ PSDPolyApprox.densityMatrices n) :
    let Z := megStep Xt (grad Xt) η
    η * (grad Xt * (Z - X)).trace ≤ ((mlog Xt - mlog Z) * (Z - X)).trace ∧
      ((mlog Xt - mlog Z) * (Z - X)).trace = bregman X Xt - bregman X Z - bregman Z Xt := by sorry

end LowRankMEG
