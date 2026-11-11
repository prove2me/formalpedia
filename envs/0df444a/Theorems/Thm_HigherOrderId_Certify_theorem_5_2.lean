-- Prove2me | Theorems.Thm_HigherOrderId_Certify_theorem_5_2
-- name    : HigherOrderId.Certify.theorem_5_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:17:55.869454+00:00
-- url     : https://prove2.me/theorems/6a683ced-e6b7-458b-8441-b503e6b8d42f
-- title:
--   Theorem 5.2 — safe-coarsening certification: the smallest certifiable tolerance over 𝔇_{d,m}(α) is ≍_{δ,β} σ²(d−m)√(d²+m⁶)/(Nα²)
-- statement:
--   Fix $\delta,\beta\in(0,1/4)$. There are constants $\bar c,c,C>0$ depending only on $(\delta,\beta)$ such that the following holds for every $d\ge10$, every integer $0\le m\le m_d=\lfloor(\sqrt{8d+1}-1)/2\rfloor$, every $\alpha\in(0,1/2]$, $\sigma>0$, every budget $N$ with $N/E$ a positive integer ($E=d-m+1$) and every $R>0$. Write
--   $$r_{d,m,N}=\frac{\sigma^2(d-m)}{N\alpha^2}\sqrt{d^2+m^6}.$$
--   If $r_{d,m,N}\le\bar cR^2$, then
--
--   - (achievability) there are a design $D\in\mathfrak D_{d,m}(\alpha)$, a tolerance $\varepsilon\in(0,R^2]$ with $\varepsilon\le C\,r_{d,m,N}$, and a measurable $\{0,1\}$-valued rule $C$ of the Gaussian value–gradient release (7) of $D$ satisfying (9):
--   $$\sup_{(b,Q)\in\Theta_R:\ V\ge\varepsilon}\Pr(C=1)\le\delta,\qquad\Pr_{b=0,Q=0}(C=1)\ge1-\beta;$$
--   - (converse) for every design $D\in\mathfrak D_{d,m}(\alpha)$, every $\varepsilon\in(0,R^2]$ and every rule satisfying (9), $\varepsilon\ge c\,r_{d,m,N}$.
--
--   Together: the smallest achievable $\varepsilon\in(0,R^2]$, optimized over designs in $\mathfrak D_{d,m}(\alpha)$ and all rules, is $\asymp_{\delta,\beta}r_{d,m,N}$. Compared with the learning rate of Theorem 5.1, certification needs the extra $m^6$ term: at the identification threshold $m\asymp\sqrt d$ the tolerance is of order $\sigma^2d^{5/2}/(N\alpha^2)$, against the full-span benchmark $\sigma^2d^2/(N\alpha^2)$.
--
--   Differences from the source:
--   - generalization: R as in model (6): 0 < R ≤ [4√(d + (d choose 2))]⁻¹ → every R > 0; reason: §B.1 states that the Gaussian experiment is defined for every R > 0 and the proof never uses the upper bound; the statement for all R > 0 contains the bounded range
--   - generalization: the converse ranges over rules C ∈ {0, 1} → every measurable acceptance function φ into [0, 1] (randomized rule), with Pr(C = 1) = ∫ φ; reason: the proof goes through Lemma C.1, whose lower bound covers randomized rules (p. 29); a measurable {0,1}-rule is the indicator special case
--   - encoding: "the smallest achievable ε ∈ (0, R²], optimized over designs D ∈ 𝔇_{d,m}(α) and all rules, is ≍_{δ,β} r_{d,m,N}" → (∃ D ∈ 𝔇, ∃ ε ∈ (0, R²] with ε ≤ C·r, ∃ measurable A with (9) for 1_A) ∧ (∀ D ∈ 𝔇, ∀ ε ∈ (0, R²], ∀ rule with (9): ε ≥ c·r), with c̄, c, C > 0 chosen after (δ, β) only; reason: explicit two-sided form of ≍_{δ,β} for an infimum over the stated class
--   - encoding: the sup over the alternative in (9); a rule C ∈ {0, 1} → a bound for every (b, Q) ∈ Θ_R with V ≥ ε; achievability rules are indicators of measurable sets of observations; reason: same condition; measurability is needed for Pr(C = 1) to be defined
--   - encoding: 𝔇_{d,m}(α): centered regular-simplex designs in a k-dimensional subspace with n_e = N/E → the printed equivalent form: ‖x_e‖₂ = α, Σ_e x_e = 0, E⁻¹Σ_e x_e x_eᵀ = (α²/k) WWᵀ with WᵀW = I_k, and n_e = N/E; reason: the paper gives this characterisation ('Equivalently', p. 5); P_V = WWᵀ for an orthonormal basis W of V
-- source:
--   Zhang, Yan, Qiao, Yu, The Higher-Order Identifiability Paradox: Learning and Certifying Hypergraph Order, STOC 2027 submission (manuscript sha256 7e0ce916…), p. 6, Theorem 5.2 (PDF p. 7); proof pp. 28–31 (PDF pp. 29–32)

import Mathlib
import Definitions.Def_HigherOrderId_Certify_Model
import Definitions.Def_HigherOrderId_Certify_Release

open MeasureTheory

namespace HigherOrderId.Certify

/-- Theorem 5.2 (a different environment threshold for safe coarsening). Fix `δ, β ∈ (0, 1/4)`.
There are constants `c̄, c, C > 0` depending only on `(δ, β)` such that for every `d ≥ 10`, every
integer `0 ≤ m ≤ m_d`, every `α ∈ (0, 1/2]`, `σ > 0`, every budget `N` with `N/E` a positive
integer (`E = d − m + 1`) and every `R > 0` with `r_{d,m,N} ≤ c̄ R²`:
(achievability) some design in `𝔇_{d,m}(α)`, some tolerance `ε ∈ (0, R²]` with `ε ≤ C r_{d,m,N}`
and some measurable `{0,1}`-rule satisfy (9) for the Gaussian value–gradient release (7); and
(converse) for every design in `𝔇_{d,m}(α)`, every `ε ∈ (0, R²]` and every rule (randomized
rules included) satisfying (9), `ε ≥ c r_{d,m,N}`. -/
theorem theorem_5_2 (δ β : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4) (hβ0 : 0 < β) (hβ1 : β < 1 / 4) :
    ∃ cbar c C : ℝ, 0 < cbar ∧ 0 < c ∧ 0 < C ∧
      ∀ (d m N : ℕ) (α σ R : ℝ), 10 ≤ d → m ≤ md d → 0 < α → α ≤ 1 / 2 → 0 < σ →
        (d - m + 1) ∣ N → 0 < N / (d - m + 1) → 0 < R →
        rate d m N α σ ≤ cbar * R ^ 2 →
        (∃ D : Design d (d - m + 1), InDesignClass d m N α D ∧
          ∃ ε : ℝ, 0 < ε ∧ ε ≤ R ^ 2 ∧ ε ≤ C * rate d m N α σ ∧
            ∃ A : Set (Obs d (d - m + 1)), MeasurableSet A ∧
              Certifies D σ R ε δ β (A.indicator (fun _ => (1 : ℝ)))) ∧
        (∀ D : Design d (d - m + 1), InDesignClass d m N α D →
          ∀ ε : ℝ, 0 < ε → ε ≤ R ^ 2 →
            ∀ φ : Obs d (d - m + 1) → ℝ, IsRandomizedRule φ →
              Certifies D σ R ε δ β φ → c * rate d m N α σ ≤ ε) := by sorry

end HigherOrderId.Certify
