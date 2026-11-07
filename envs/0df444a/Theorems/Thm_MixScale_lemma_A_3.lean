-- Prove2me | Theorems.Thm_MixScale_lemma_A_3
-- name    : MixScale.lemma_A_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:10:46.28449+00:00
-- url     : https://prove2.me/theorems/4c6e8528-02aa-4ae8-aab2-ce878851392f
-- title:
--   Lemma A.3, p.15 — stable coefficient inversion
-- statement:
--   Under Definition A.1 and the scalar bounds (17), let $a_j=c_0w_jv_j^{-q/2}$ and $c_j=\lambda a_jv_j^{-\alpha/2}$. There are constants $C,D$ depending only on the profile such that, with $\mathsf P=C(kMK/w_\star)^D$:
--
--   1. $v_j=(\lambda a_j/c_j)^{2/\alpha}$ and $w_j=a_jv_j^{q/2}/c_0$;
--   2. $a_j\in[a_*,A]$ and $c_j\in[c_*,c^*]$, and clipping tentative values to these intervals does not increase the error;
--   3. on the rectangle $[a_*,A]\times[c_*,c^*]$ both inverse maps are $\mathsf P$-Lipschitz;
--   4. if $|\hat a-a_j|\le\eta$ and $|\hat c-c_j|\le\eta$, then after clipping $\hat a,\hat c$ to the rectangle and the readouts to $[K^{-1},K]$ and $[w_\star,1]$, the scale and weight errors are at most $\mathsf P\eta$.
--
--   This is the final readout of the scale and weight from the fitted coefficients in the unrestricted class.
--
--   Differences from the source:
--   - encoding: a known polynomial Lipschitz constant, P in (k, M, K, w★⁻¹) with profile-dependent constants → C(kMK/w★)^D, with C, D chosen after the profile and before all other data; reason: p.14 convention; all variables are ≥ 1 on the inputs
--   - encoding: w★ of (17) → 0 < w★; reason: the standing assumption of (2)
--   - encoding: coefficient errors at most η_coef; Lipschitz constant → per-coordinate errors |â − a|, |ĉ − c| ≤ η; Lipschitz in the larger of the two coordinate differences; reason: the paper does not fix the norm; polynomial factors absorb any choice
-- source:
--   Wang–Zhang, Learning Mixtures with Unknown Scales: Sharp Dependence on Separation, STOC 2027 submission (sha256 5277f95e…), Lemma A.3, p.15 (PDF p.17); (17)–(18), p.14

import Mathlib
import Definitions.Def_MixScale_Model
import Definitions.Def_MixScale_Scalar

namespace MixScale

/-- **Lemma A.3** (Stable coefficient inversion).

S. Wang and X. Zhang, *Learning Mixtures with Unknown Scales: Sharp Dependence on Separation*, STOC
2027 submission manuscript (sha256 5277f95e…7c6c), Lemma A.3, p.15 (PDF p.17), with (17)–(18), p.14.

In the scalar setting (17), for the coefficients `a_j, c_j` of (18):
1. `v_j = (λa_j/c_j)^{2/α}`, `w_j = a_j v_j^{q/2}/c₀`;
2. the true coefficients lie in `[a∗, A]`, `[c∗, c^∗]`, and clipping to these intervals does not
   increase the coordinate error;
3. the inverse map is Lipschitz on this rectangle with constant `P`;
4. coefficient errors at most `η` imply scale and weight errors at most `P η`, after clipping the
   readout to `[K⁻¹, K]` and `[w★, 1]`.

**Formalization Note.** `P = C (k M K / w★)^D` with `C, D` depending on the profile only (p.14: "the
condition polynomials depend on `(k, M, K, w★⁻¹)`"). `w★ > 0` is the standing assumption of (2). The
Lipschitz bound is with respect to the larger of the two coordinate differences. -/
theorem lemma_A_3 (S : ProfileSpec) (hS : IsEffectiveProfile S) :
    ∃ (C : ℝ) (D : ℕ), 0 < C ∧
      ∀ (k : ℕ) (M K Δ wstar : ℝ) (b v w : Fin k → ℝ), 0 < wstar → Scalar17 M K Δ wstar b v w →
      ∀ j : Fin k,
        v j = invScale S (ampl S (w j) (v j)) (corr S (w j) (v j)) ∧
        w j = invWeight S (ampl S (w j) (v j)) (corr S (w j) (v j)) ∧
        ampl S (w j) (v j) ∈ Set.Icc (aLow S wstar K) (aHigh S K) ∧
        corr S (w j) (v j) ∈ Set.Icc (cLow S wstar K) (cHigh S K) ∧
        (∀ x : ℝ, |clip (aLow S wstar K) (aHigh S K) x - ampl S (w j) (v j)| ≤
          |x - ampl S (w j) (v j)|) ∧
        (∀ x : ℝ, |clip (cLow S wstar K) (cHigh S K) x - corr S (w j) (v j)| ≤
          |x - corr S (w j) (v j)|) ∧
        (∀ a₁ ∈ Set.Icc (aLow S wstar K) (aHigh S K), ∀ a₂ ∈ Set.Icc (aLow S wstar K) (aHigh S K),
          ∀ c₁ ∈ Set.Icc (cLow S wstar K) (cHigh S K), ∀ c₂ ∈ Set.Icc (cLow S wstar K) (cHigh S K),
            |invScale S a₁ c₁ - invScale S a₂ c₂| ≤
                C * ((k : ℝ) * M * K / wstar) ^ D * max |a₁ - a₂| |c₁ - c₂| ∧
            |invWeight S a₁ c₁ - invWeight S a₂ c₂| ≤
                C * ((k : ℝ) * M * K / wstar) ^ D * max |a₁ - a₂| |c₁ - c₂|) ∧
        ∀ η ahat chat : ℝ, |ahat - ampl S (w j) (v j)| ≤ η → |chat - corr S (w j) (v j)| ≤ η →
          |clip K⁻¹ K (invScale S (clip (aLow S wstar K) (aHigh S K) ahat)
              (clip (cLow S wstar K) (cHigh S K) chat)) - v j| ≤
            C * ((k : ℝ) * M * K / wstar) ^ D * η ∧
          |clip wstar 1 (invWeight S (clip (aLow S wstar K) (aHigh S K) ahat)
              (clip (cLow S wstar K) (cHigh S K) chat)) - w j| ≤
            C * ((k : ℝ) * M * K / wstar) ^ D * η := by sorry

end MixScale
