-- Prove2me | Theorems.Thm_LowDimMeanEst_lemma_25
-- name    : LowDimMeanEst.lemma_25
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:56:12.867859+00:00
-- url     : https://prove2.me/theorems/0eaec327-20d0-4a8d-b22d-55639a43a1f1
-- title:
--   Lemma 25 — an $\epsilon$-net in operator norm of $\{A\succeq0:\mathrm{Tr}(A)\le R\}$ of size $\le(1000R/\epsilon)^{d(d+1)/2}$
-- statement:
--   **Lemma 25.** Let $d\ge1$ and $R>\epsilon>0$. There is a finite set $Z_\epsilon$ of symmetric positive semidefinite $d\times d$ matrices with trace at most $R$ such that every $A\succeq0$ with $\mathrm{Tr}(A)\le R$ has some $A_{\rm net}\in Z_\epsilon$ with
--
--   $$\|A_{\rm net}-A\|_{op}\le\epsilon,$$
--
--   and
--
--   $$|Z_\epsilon|\ \le\ \Big(\frac{1000R}{\epsilon}\Big)^{d(d+1)/2}.$$
--
--   This net over small-trace matrices is the first of the two net arguments of §8.
--
--   Differences from the source:
--   - encoding: d × d matrices with ∥·∥op → continuous linear maps of ℝ^d with the operator norm; A ⪰ 0 as IsPositive; reason: the same objects
-- source:
--   Lee, Mathashery, Valiant, Wang, Optimal Sub-Gaussian Mean Estimation in Low Dimensions, STOC 2027 submission (manuscript sha256 7316d30e…), Lemma 25, p.30 (proof pp.30–31)

import Mathlib
import Definitions.Def_LowDimMeanEst_Basic

namespace LowDimMeanEst

/-- **Lemma 25**, p.30 (proof pp.30–31).

Lee, Mathashery, Valiant, Wang, *Optimal Sub-Gaussian Mean Estimation in Low Dimensions*, STOC 2027
submission (manuscript sha256 7316d30e…).

"Consider dimension d ≥ 1 and constants R > ϵ > 0. There exists a matrix net Z_ϵ of dimension d
square matrices A′ ⪰ 0 and Tr(A′) ≤ R such that for any matrix A ⪰ 0 such that Tr(A) ≤ R, there
exists a matrix A_net ∈ Z_ϵ such that ∥A_net − A∥op ≤ ϵ. Moreover, there exists such a set Z_ϵ whose
size is bounded above by (1000R/ϵ)^{d(d+1)/2}."

**Formalization Note.** Matrices are maps `E d →L[ℝ] E d` with the operator norm; "`A ⪰ 0`" is
symmetric positive semidefinite (`IsPositive`). The exponent `d(d+1)/2` is a natural number. One set
`Z` has all three properties.
-/
theorem lemma_25 (d : ℕ) (hd : 1 ≤ d) (R ε : ℝ) (hε : 0 < ε) (hεR : ε < R) :
    ∃ Z : Finset (E d →L[ℝ] E d),
      (∀ A' ∈ Z, A'.IsPositive ∧ tr A' ≤ R) ∧
      (∀ A : E d →L[ℝ] E d, A.IsPositive → tr A ≤ R → ∃ Anet ∈ Z, ‖Anet - A‖ ≤ ε) ∧
      (Z.card : ℝ) ≤ (1000 * R / ε) ^ (d * (d + 1) / 2) := by sorry

end LowDimMeanEst
