-- Prove2me | Theorems.Thm_LowRankMEG_eq_29
-- name    : LowRankMEG.eq_29
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:51:04.764368+00:00
-- url     : https://prove2.me/theorems/db3ec38b-da63-4fc2-9357-e3fc4944ca54
-- title:
--   (29) — the bound on $-\log\operatorname{Tr}Y$
-- statement:
--   Let $X^*$ be optimal, let $X\in\mathcal S_n$, $X\succ0$, let $D$ be symmetric with $\|D-\nabla f(X)\|_2\le\xi$, let $\eta>0$, and let $Y=\exp(\log(X)-\eta D)$. Then
--   $$
--   -\log\sum_{i=1}^n\lambda_i(Y)\le\eta\lambda_n(\nabla f(X^*))+\eta\|X-X^*\|_*\|\nabla f(X^*)\|_2+\eta\bigl(\xi+\beta\|X-X^*\|_*\bigr).
--   $$
--   With (26), this bounds the eigenvalue ratio of Lemma 2.
--
--   Differences from the source:
--   - encoding: ∇̃ ∈ 𝕊ⁿ of Lemma 3 → D symmetric; reason: notation
--   - generalization: stated inside Lemma 3, under Assumption 1 and (19) → only X* optimal, X ≻ 0 in 𝒮_n and ‖D − ∇f(X)‖₂ ≤ ξ; reason: the derivation on p.16 uses none of the others
--   - encoding: the gradient ∇f → a map grad tied to f by HasFDerivAt at symmetric matrices (Setting.hasGrad); reason: Lean needs ∇f as data; same instances
--   - encoding: λ_i with 1-based index → lam X i, with value 0 outside 1 ≤ i ≤ n; reason: every index used is in range under the hypotheses
--   - encoding: ξ ≥ 0 → no sign condition on ξ; reason: it follows from ‖D − ∇f(X)‖₂ ≤ ξ
-- source:
--   Garber & Kaplan, On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for Low-Rank Matrix Optimization, arXiv:2012.10469v2, Eq. (29), p.16

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

/-- **Eq. (29)**: with `Y = exp(log(X) − ηD)`, `‖D − ∇f(X)‖₂ ≤ ξ`,
`−log ∑_{i=1}^n λ_i(Y) ≤ ηλ_n(∇f(X*)) + η‖X − X*‖_*‖∇f(X*)‖₂ + η(ξ + β‖X − X*‖_*)`.
Garber & Kaplan, *On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for
Low-Rank Matrix Optimization*, arXiv:2012.10469v2, Eq. (29), p.16, in the proof of Lemma 3.

**Formalization Note.** It uses no strict complementarity and no ball around `X*`. -/
theorem eq_29 {n : ℕ} {f : Matrix (Fin n) (Fin n) ℝ → ℝ}
    {grad : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ} {β : ℝ}
    (hS : Setting f grad β)
    {Xs X D : Matrix (Fin n) (Fin n) ℝ} (hopt : IsOptimal f Xs)
    (hX : X ∈ PSDPolyApprox.densityMatrices n) (hXpd : X.PosDef) (hD : D.IsSymm) {ξ η : ℝ}
    (hDξ : WainwrightHDS.NucNorm.opNorm2 (D - grad X) ≤ ξ) (hη : 0 < η) :
    -Real.log (∑ i ∈ Finset.Icc 1 n, lam (mexp (mlog X - η • D)) i) ≤
      η * lam (grad Xs) n + η * WainwrightHDS.NucNorm.nucNorm (X - Xs) * WainwrightHDS.NucNorm.opNorm2 (grad Xs)
        + η * (ξ + β * WainwrightHDS.NucNorm.nucNorm (X - Xs)) := by sorry

end LowRankMEG
