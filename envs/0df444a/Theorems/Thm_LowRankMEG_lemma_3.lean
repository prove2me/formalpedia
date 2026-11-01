-- Prove2me | Theorems.Thm_LowRankMEG_lemma_3
-- name    : LowRankMEG.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:52:42.689832+00:00
-- url     : https://prove2.me/theorems/29125c94-d379-4be7-bc64-f9e37cad387b
-- title:
--   Lemma 3 — near $X^*$ the low-rank error is at most $2\varepsilon$
-- statement:
--   Let $X^*$ be optimal with Assumption 1 for $\delta>0$, let $r^*=\operatorname{rank}(X^*)$ and $r^*\le r<n$. Let $X\in\mathcal S_n$, $X\succ0$ satisfy $\lambda_{r^*+1}(X)\le\varepsilon_-/(n-r)$ for some $\varepsilon_-\in(0,1]$, let $\widetilde\nabla\in\mathbb S^n$ satisfy $\|\widetilde\nabla-\nabla f(X)\|_2\le\xi$ for some $\xi\ge0$, let $G\ge\sup_{\mathcal S_n}\|\nabla f\|_2$, $\eta>0$ and $\varepsilon\in(0,3/4]$. If condition (19) holds, then $Y=\exp(\log(X)-\eta\widetilde\nabla)$ and $b=\sum_{i=1}^n\lambda_i(Y)$ satisfy
--   $$
--   \log\frac{(n-r)\lambda_{r+1}(Y)}{\varepsilon b}\le2\varepsilon.\tag{20}
--   $$
--   As a result, for $Z_+:=Y/b$ and every low-rank update $X_+$ of (9),
--   $$
--   \max\{B(X^*,X_+)-B(X^*,Z_+),\ B(Z_+,X_+)\}\le2\varepsilon.
--   $$
--   This is the central estimate: under strict complementarity a low-rank step approximates the exact step within $2\varepsilon$ on a ball around $X^*$.
--
--   Differences from the source:
--   - generalization: G = sup over 𝒮_n of ‖∇f‖₂ → G any upper bound on it; reason: the page's G is one such bound, and Theorem 5 invokes the lemma with G ≥ sup
--   - reading: ε is not bound in the statement → ε ∈ (0, 3/4]; reason: it is the range of Lemma 2, which the last sentence invokes
--   - encoding: ε₋ ∈ [0, 1] → ε₋ ∈ (0, 1]; reason: ε₋ = 0 contradicts X ≻ 0 and makes log(ε₋/ε) undefined; excludes an undefined case only
--   - reading: ‖∇̃ − ∇f(X)‖ without subscript → the spectral norm; reason: the proof uses it as such, (23)
--   - encoding: η introduced after (19) → η a binder before (19); reason: (19) mentions η, so it is fixed first
--   - encoding: Z₊ := Y/b → megStep X D η; reason: b = Tr(Y)
--   - encoding: the gradient ∇f → a map grad tied to f by HasFDerivAt at symmetric matrices (Setting.hasGrad); reason: Lean needs ∇f as data; same instances
--   - encoding: λ_i with 1-based index → lam X i, with value 0 outside 1 ≤ i ≤ n; reason: every index used is in range under the hypotheses
-- source:
--   Garber & Kaplan, On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for Low-Rank Matrix Optimization, arXiv:2012.10469v2, Lemma 3, p.15

import Mathlib
import Definitions.Def_LowRankMEG_Setting
import Definitions.Def_LowRankMEG_IsOptimal
import Definitions.Def_LowRankMEG_StrictComplementarity
import Definitions.Def_PSDPolyApprox_densityMatrices
import Definitions.Def_LowRankMEG_bregman
import Definitions.Def_LowRankMEG_lam
import Definitions.Def_LowRankMEG_mlog
import Definitions.Def_LowRankMEG_mexp
import Definitions.Def_LowRankMEG_megStep
import Definitions.Def_LowRankMEG_IsLowRankUpdate
import Definitions.Def_LowRankMEG_Cond19
import Definitions.Def_WainwrightHDS_NucNorm_opNorm2

namespace LowRankMEG

/-- **Lemma 3**: near an optimal `X*` satisfying Assumption 1, if `λ_{r*+1}(X) ≤ ε₋/(n − r)` and (19) holds, then
`Y = exp(log(X) − ηD)` and `b = ∑_{i=1}^n λ_i(Y)` satisfy `log((n − r)λ_{r+1}(Y)/(εb)) ≤ 2ε`, Eq. (20), and for
`Z₊ := Y/b` and `X₊` as in (9), `max{B(X*, X₊) − B(X*, Z₊), B(Z₊, X₊)} ≤ 2ε`.
Garber & Kaplan, *On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for
Low-Rank Matrix Optimization*, arXiv:2012.10469v2, Lemma 3, p.15.

**Formalization Note.** `D` is the page's `∇̃`, `εm` its `ε₋`. `ε ∈ (0, 3/4]`, which the page does not bind, is
the range of Lemma 2, which the last sentence invokes. `ε₋ ∈ (0, 1]`: `ε₋ = 0` contradicts `X ≻ 0`. `G` is any upper
bound on `‖∇f‖₂` over `𝒮_n`; the page's `G` is the supremum. `η` comes before (19), which mentions it.
`Z₊ = Y/b` is `megStep X D η`, as `b = Tr Y`. -/
theorem lemma_3 {n : ℕ} {f : Matrix (Fin n) (Fin n) ℝ → ℝ}
    {grad : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ} {β : ℝ}
    (hS : Setting f grad β)
    {Xs X D : Matrix (Fin n) (Fin n) ℝ} {δ G ξ η εm ε : ℝ} {r : ℕ}
    (hopt : IsOptimal f Xs) (hsc : StrictComplementarity grad Xs δ)
    (hrs : Xs.rank ≤ r) (hrn : r < n)
    (hX : X ∈ PSDPolyApprox.densityMatrices n) (hXpd : X.PosDef) (hεm : εm ∈ Set.Ioc (0 : ℝ) 1)
    (hlam : lam X (Xs.rank + 1) ≤ εm / ((n : ℝ) - r))
    (hD : D.IsSymm) (hξ : 0 ≤ ξ) (hDξ : WainwrightHDS.NucNorm.opNorm2 (D - grad X) ≤ ξ)
    (hG : ∀ W ∈ PSDPolyApprox.densityMatrices n, WainwrightHDS.NucNorm.opNorm2 (grad W) ≤ G)
    (hη : 0 < η) (hε : ε ∈ Set.Ioc (0 : ℝ) (3 / 4))
    (h19 : Cond19 β G δ Xs η εm ε ξ X) :
    let Y := mexp (mlog X - η • D)
    let b := ∑ i ∈ Finset.Icc 1 n, lam Y i
    Real.log (((n : ℝ) - r) * lam Y (r + 1) / (ε * b)) ≤ 2 * ε ∧
      ∀ Xp, IsLowRankUpdate X D η ε r Xp →
        max (bregman Xs Xp - bregman Xs (megStep X D η)) (bregman (megStep X D η) Xp)
          ≤ 2 * ε := by sorry

end LowRankMEG
