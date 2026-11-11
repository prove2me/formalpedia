-- Prove2me | Theorems.Thm_HigherOrderId_Certify_lemma_C_1
-- name    : HigherOrderId.Certify.lemma_C_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:17:33.204472+00:00
-- url     : https://prove2.me/theorems/bf7d1b67-fa1b-4940-be9c-b7cd189bd394
-- title:
--   Lemma C.1 — matching Gaussian safety–power boundary for certifying ‖ϑ‖² < ε
-- statement:
--   Let $X\sim N(\vartheta,\Sigma)$ on $\mathbb R^D$ with $\Sigma\succ0$ known and $\|\vartheta\|_2^2\le R^2$, and put $F=\|\Sigma\|_F$. Fix $\delta,\beta\in(0,1/4)$ (so $\delta+\beta<1$) and $0<\varepsilon\le R^2$.
--
--   1. If a rule is $(\varepsilon,\delta)$-safe (89) and has null power at least $1-\beta$, then
--   $$\varepsilon\ \ge\ c_{\delta,\beta}F,\qquad c_{\delta,\beta}=\big[2\log\{1+4(1-\delta-\beta)^2\}\big]^{1/2}.$$
--   2. Conversely, if $\varepsilon\ge C_{\delta,\beta}F$ with $C_{\delta,\beta}=\max\{\sqrt{8/\beta},32/\delta\}$, then the rule $\phi_\varepsilon(X)=\mathbf 1\{\|X\|_2^2-\operatorname{tr}\Sigma\le\varepsilon/2\}$ is $(\varepsilon,\delta)$-safe and has null power at least $1-\beta$.
--
--   This is the Gaussian testing core of Theorem 5.2: the certification tolerance for the omitted energy is, up to $(\delta,\beta)$-constants, the Frobenius norm of the noise covariance. Part 1 also holds for randomized rules, which the Lean statement covers.
--
--   Differences from the source:
--   - generalization: a rule ϕ(X) ∈ {0, 1} in part (90) → every measurable acceptance function into [0, 1] (randomized rule), with P_ϑ{ϕ = 1} read as ∫ ϕ dN(ϑ, Σ); reason: the paper's proof covers randomized rules (p. 29); a measurable {0,1}-rule is the special case of an indicator
--   - encoding: hypothesis δ + β < 1 → omitted; reason: implied by δ, β ∈ (0, 1/4); no instance changes
--   - encoding: X ∼ N(ϑ, Σ) on R^D; a rule ϕ(X) ∈ {0,1} → multivariateGaussian ϑ Σ on EuclideanSpace ℝ (Fin D); rules are measurable real functions; reason: Mathlib's Gaussian; measurability is needed for P_ϑ{ϕ(X) = 1} to be defined
--   - encoding: M := ‖Σ‖_op is defined in the setting → not present; reason: M occurs only in the proof, not in the statement
-- source:
--   Zhang, Yan, Qiao, Yu, The Higher-Order Identifiability Paradox: Learning and Certifying Hypergraph Order, STOC 2027 submission (manuscript sha256 7e0ce916…), p. 28, Lemma C.1 (PDF p. 29)

import Mathlib
import Definitions.Def_HigherOrderId_Certify_Model
import Definitions.Def_HigherOrderId_Certify_GaussTest

open MeasureTheory ProbabilityTheory

namespace HigherOrderId.Certify

/-- Lemma C.1 (matching Gaussian safety–power boundary). For `X ∼ N(ϑ, Σ)` on `ℝ^D` with
`Σ ≻ 0` known, `F = ‖Σ‖_F`, `δ, β ∈ (0, 1/4)` and `0 < ε ≤ R²`: every rule (randomized rules
allowed) that is `(ε, δ)`-safe with null power at least `1 − β` forces `ε ≥ c_{δ,β} F`; and if
`ε ≥ C_{δ,β} F`, the rule `1{‖X‖₂² − tr Σ ≤ ε/2}` is `(ε, δ)`-safe with null power at least
`1 − β`. -/
theorem lemma_C_1 (D : ℕ) (S : Matrix (Fin D) (Fin D) ℝ) (hS : S.PosDef)
    (δ β R ε : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4) (hβ0 : 0 < β) (hβ1 : β < 1 / 4)
    (hε0 : 0 < ε) (hεR : ε ≤ R ^ 2) :
    (∀ φ : EuclideanSpace ℝ (Fin D) → ℝ, IsRandomizedRule φ → IsSafe S R ε δ φ →
        1 - β ≤ nullPower S φ → cLower δ β * frobNorm S ≤ ε) ∧
    (CUpper δ β * frobNorm S ≤ ε →
        IsSafe S R ε δ (energyRule S ε) ∧ 1 - β ≤ nullPower S (energyRule S ε)) := by sorry

end HigherOrderId.Certify
