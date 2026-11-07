-- Prove2me | Theorems.Thm_LowTempGlauber_lemma_14
-- name    : LowTempGlauber.lemma_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:26:59.031925+00:00
-- url     : https://prove2.me/theorems/5e15e557-2418-4c12-a9f1-fcaad54dade6
-- title:
--   Lemma 14 — a phase selector from upper-$\delta$-tailed estimators, within $4\delta$ of $Z^+/(Z^++Z^-)$ using $2L+2$ samples
-- statement:
--   Let $\delta\in(0,1/4)$ and $L=\lceil64\log(1/\delta)\rceil$. There is an algorithm which, given $L+1$ independent samples of each of two estimators $W^+$ and $W^-$ and independent auxiliary randomness, outputs a sign $\sigma\in\{+,-\}$ with the following guarantee: whenever $W^+$ and $W^-$ are upper-$\delta$-tailed estimators (Definition 13) for quantities $Z^+,Z^-\ge0$ with $Z^++Z^->0$,
--   $$\Bigl|\Pr(\sigma=+)-\frac{Z^+}{Z^++Z^-}\Bigr|\le4\delta,$$
--   i.e. the law of $\sigma$ is within $4\delta$ in total variation of the law $\Pr(+)=\frac{Z^+}{Z^++Z^-}$, $\Pr(-)=\frac{Z^-}{Z^++Z^-}$. In particular it uses at most $2L+2$ samples of the estimators.
--
--   The selector chooses the phase of the full sample in Theorem 1, part 2, without estimating the phase partition functions to the final accuracy.
--
--   **Formalization Note** The algorithm is a measurable map of $L+1$ samples of $W^+$, $L+1$ samples of $W^-$ and a sequence of independent uniform $[0,1]$ variables; it is chosen knowing $\delta$ only, before $Z^\pm$ and $W^\pm$. $\log$ is the natural logarithm.
--
--   Differences from the source:
--   - generalization: "an algorithm using at most 2L + 2 independent samples from the estimators" → a measurable map of exactly L + 1 samples of W⁺ and L + 1 samples of W⁻ and an independent uniform sequence, fixed before Z± and W±; reason: such a map is an algorithm using at most 2L + 2 samples (the proof’s algorithm has this form), so the Lean statement implies the source’s
--   - encoding: TV distance on {+, −}; the target distribution Z±/(Z⁺ + Z⁻) → |Pr(σ = +) − Z⁺/(Z⁺ + Z⁻)| with hypothesis Z⁺ + Z⁻ > 0; reason: on a two-point space TV is this difference; the target law is undefined when Z⁺ = Z⁻ = 0
-- source:
--   Galanis–Štefankovič, Low-Temperature Sampling via Equilibrium Disagreements, STOC 2027 submission (manuscript sha256 c41a38ff…7533d), Definition 13 and Lemma 14, p.15 (proof pp.15–16)

import Mathlib
import Definitions.Def_LowTempGlauber_Gibbs

namespace LowTempGlauber

open MeasureTheory

/-- Galanis–Štefankovič, *Low-Temperature Sampling via Equilibrium Disagreements*, STOC 2027
submission (manuscript sha256 c41a38ff…), Lemma 14 with Definition 13, p.15 (proof pp.15–16).

Suppose we have upper-`δ`-tailed estimators `W⁺, W⁻` for `Z⁺, Z⁻`. Then there is an algorithm using at
most `2L + 2` independent samples from the estimators, where `L = ⌈64 log(1/δ)⌉`, whose output
`σ ∈ {+, −}` is within `4δ` in TV-distance of the law `Pr(σ = +) = Z⁺/(Z⁺ + Z⁻)`,
`Pr(σ = −) = Z⁻/(Z⁺ + Z⁻)`.

**Formalization Note.** The algorithm is a measurable map `Φ` (chosen knowing `δ` only, before
`Z±, W±`) of `L + 1` samples of `W⁺`, `L + 1` samples of `W⁻` and an independent sequence of uniform
`[0, 1]` variables (its auxiliary randomness); `true` is `+`. The samples are independent: the law is
the product `(W⁺)^{⊗(L+1)} ⊗ (W⁻)^{⊗(L+1)} ⊗ U[0,1]^{⊗ℕ}`. On `{+, −}` the TV distance is
`|Pr(σ = +) − Z⁺/(Z⁺ + Z⁻)|`. `Z⁺ + Z⁻ > 0` excludes the case where the target law is undefined.
`log` is natural (the proof uses `e^{−L/64} ≤ δ`). -/
theorem lemma_14 (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4) :
    ∃ Φ : (Fin (⌈64 * Real.log (1 / δ)⌉₊ + 1) → ℝ) × (Fin (⌈64 * Real.log (1 / δ)⌉₊ + 1) → ℝ) ×
        (ℕ → unitInterval) → Bool,
      Measurable Φ ∧
        ∀ (Zp Zm : ℝ) (Wp Wm : Measure ℝ) [IsProbabilityMeasure Wp] [IsProbabilityMeasure Wm],
          0 ≤ Zp → 0 ≤ Zm → 0 < Zp + Zm →
          IsUpperTailed δ Zp Wp → IsUpperTailed δ Zm Wm →
          |(((Measure.pi fun _ : Fin (⌈64 * Real.log (1 / δ)⌉₊ + 1) => Wp).prod
                ((Measure.pi fun _ : Fin (⌈64 * Real.log (1 / δ)⌉₊ + 1) => Wm).prod
                  (Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval))))
                {x | Φ x = true}).toReal - Zp / (Zp + Zm)| ≤ 4 * δ := by sorry

end LowTempGlauber
