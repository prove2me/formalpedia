-- Prove2me | Theorems.Thm_MixScale_lemma_H_1
-- name    : MixScale.lemma_H_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:11:13.557403+00:00
-- url     : https://prove2.me/theorems/9b7bd252-c162-4d3a-abb2-55249f6ff487
-- title:
--   Lemma H.1, p.49 — equal-weight readout
-- statement:
--   Under Definition A.1 and (17), let all weights equal $1/k$. Suppose an estimate $(\hat a_j,\hat\zeta_j,\hat\beta_j)$ of the scaled coordinates (21) (with $\zeta_j=c_j/R^\alpha$, $\beta_j=Rb_j$) has Euclidean error at most $t$. Clip $\hat a_j$ to $[(c_0/k)K^{-q/2},(c_0/k)K^{q/2}]$ and set $\hat v_j=(c_0/(k\hat a_j))^{2/q}$, $\hat b_j=\hat\beta_j/R$. Then
--
--   $$|\hat b_j-b_j|\le t/R,\qquad|\hat v_j-v_j|\le L_at,\qquad L_a=\frac{2k}{qc_0}K^{1+q/2}.$$
--
--   Scale recovery therefore uses the leading amplitudes alone, which is what removes the factor $\gamma^{-2\alpha}$ in the equal-weight class.
--
--   Differences from the source:
--   - generalization: R ≥ 1, the local frequency of (21) → R > 0; reason: the bound uses only R > 0; R ≥ 1 is a special case
--   - encoding: Euclidean error; ŵ_j = 1/k; "under the same component matching" → error over all 3k coordinates, indexed like the truth; the weight is 1/k by hypothesis and carries no error; reason: the index is the matching; the true weight is the output weight
-- source:
--   Wang–Zhang, Learning Mixtures with Unknown Scales: Sharp Dependence on Separation, STOC 2027 submission (sha256 5277f95e…), Lemma H.1, p.49 (PDF p.51); (17), (18), (21)

import Mathlib
import Definitions.Def_MixScale_Model
import Definitions.Def_MixScale_Scalar

namespace MixScale

/-- **Lemma H.1** (Equal-weight readout).

S. Wang and X. Zhang, *Learning Mixtures with Unknown Scales: Sharp Dependence on Separation*, STOC
2027 submission manuscript (sha256 5277f95e…7c6c), Lemma H.1, p.49 (PDF p.51), with (17), (18), (21).

**Formalization Note.** `R > 0` is the local frequency of (21) (the paper's `R ≥ 1` is a special
case). The estimate `(â, ζ̂, β̂)` is indexed like the truth ("the same component matching as the
coordinate guarantee"). Its error is Euclidean over all `3k` coordinates. The clipped amplitude is
`clip a^{eq}_− a^{eq}_+ â_j`, the output (95) is written out, and `ŵ_j = 1/k` is the true weight by
hypothesis. -/
theorem lemma_H_1 (S : ProfileSpec) (hS : IsEffectiveProfile S) (k : ℕ) (M K Δ wstar : ℝ)
    (b v w : Fin k → ℝ) (hsc : Scalar17 M K Δ wstar b v w) (hw : ∀ j, w j = 1 / (k : ℝ))
    (R : ℝ) (hR : 0 < R) (t : ℝ) (ahat ζhat βhat : Fin k → ℝ)
    (ht : Real.sqrt (∑ j, ((ahat j - ampl S (w j) (v j)) ^ 2 +
      (ζhat j - corr S (w j) (v j) / R ^ S.α) ^ 2 + (βhat j - R * b j) ^ 2)) ≤ t) (j : Fin k) :
    |βhat j / R - b j| ≤ t / R ∧
    |(S.c0 / ((k : ℝ) * clip (S.c0 / k * K ^ (-S.q / 2)) (S.c0 / k * K ^ (S.q / 2)) (ahat j))) ^
        (2 / S.q) - v j| ≤ (2 * k / (S.q * S.c0)) * K ^ (1 + S.q / 2) * t := by sorry

end MixScale
