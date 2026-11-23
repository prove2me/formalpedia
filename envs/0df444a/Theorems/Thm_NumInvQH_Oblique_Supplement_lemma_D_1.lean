-- Prove2me | Theorems.Thm_NumInvQH_Oblique_Supplement_lemma_D_1
-- name    : NumInvQH.Oblique.Supplement.lemma_D_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T21:47:07.143823+00:00
-- url     : https://prove2.me/theorems/f22fba8b-d87f-422e-a9c8-edd9323a83ac
-- title:
--   Lemma D.1 (corrected: source conventions) — all characteristic and objective transformations
-- statement:
--   Use the Appendix D setting $S=(X,Y)$, $\widehat S=S/X$ and $d\widehat P/dP=X_T^2/E[X_T^2]$, with local square integrability under the respective measures. Let $L,V$ and $\widehat L,\widehat V$ be the indicated semimartingales, with $L_-,\widehat L_->0$, and suppose $L=\widehat L\widetilde Z/X^2$, $V=X\widehat V$. Let the weighted rates $\bar b,\bar C,\bar u,\bar\gamma$ and $\widehat b,\widehat C,\widehat u,\widehat\gamma$ be those defined on p. 35, relative to one common clock. Write $x=X_-$, $s=S_-$, $v=V_-$, $\widehat v=\widehat V_-$, and let $\ell,\widehat\ell$ be the differential drifts of the stochastic logarithms of $L,\widehat L$. Then all of (D.1)–(D.5) hold:
--   $$\widehat\ell=\ell+2\bar b^X/x+\bar C^{XX}/x^2,$$
--   $$\widehat b_i=(\bar b_i+\bar C_{iX}/x-s_i(\bar b_X+\bar C_{XX}/x)/x)/x,$$
--   $$\widehat C_{ij}=(\bar C_{ij}-(s_i\bar C_{Xj}+\bar C_{iX}s_j)/x+\bar C_{XX}s_is_j/x^2)/x^2,$$
--   $$\widehat u_i=(\bar u_i-(s_i\bar u_X+\bar C_{iX}v)/x+\bar C_{XX}vs_i/x^2)/x^2,$$
--   $$\widehat\gamma=(\bar\gamma-2\widehat v\bar u_X+\widehat v^2\bar C_{XX})/x^2.$$
--   Moreover the entire constrained objectives transform as
--   $$\theta\widehat C\theta^\top-2\theta\widehat b+\widehat\ell=x^{-2}\theta\bar C\theta^\top-2x^{-1}\theta\bar b+\ell\quad(\theta\widehat S_-=-1),$$
--   $$\theta\widehat C\theta^\top-2\theta\widehat u+\widehat\gamma=x^{-2}(\theta\bar C\theta^\top-2\theta\bar u+\bar\gamma)\quad(\theta\widehat S_-=\widehat V_-).$$
--   Equalities of rates hold almost everywhere for the common random clock. These identities transfer both quadratic programs, including their linear and constant terms.
--
--   The initial sigma field is $P$-trivial, as in the standing setting on p. 2.
--
--   Differences from the source:
--   - encoding: finite-horizon vector processes and stochastic equality → Fin-indexed coordinates, stopped extensions and indistinguishability on [0,T]; reason: this preserves the full finite-horizon domain, including null modifications and arbitrary finite dimension d ≥ 2
--   - encoding: the general predictable vector integral of [22, III.6.17] → elementary-sum construction followed by bounded predictable extension and Emery convergence of joint truncations; reason: this constructs general vector integration and retains cancellation; it does not impose coordinatewise integrability, absolute continuity of characteristics, or calculus axioms
--   - encoding: stochastic integrals, brackets, logarithms, exponentials and conditional processes → chosen genuine versions from explicit defining relations; reason: these quantities are unique up to indistinguishability on the stated domain; their outside-domain zero defaults are not hypotheses or replacement values for source objects
--   - encoding: weighted drift and covariance formulas involving c and F → the exactly equivalent compensator-rate identities (D.8)–(D.11); reason: the source proves these identities on pp. 35–36; normalization by 1+ΔB retains (4.1), (4.2), (4.8) and (4.10) for arbitrary clocks and jumps
--   - correction: the constraint θŜ_-=V̂ in (D.7) → θŜ_-=V̂_-; reason: the proof on p.36 explicitly uses θS_-=V_- iff θŜ_-=V̂_-; the displayed constraint has lost its left-limit mark
--   - encoding: the stochastic logarithms in the well-defined weighted rates of Lemma D.1 and the as-above data of Lemma D.2 → LogDefined requires existence of the actual defining stochastic integral; WeightedRates carries that guard and Lemma D.2 names it explicitly; reason: positive left limits alone do not justify a logarithm after a zero-and-recovery path; this retains the source definedness requirement instead of accepting a zero fallback, and excludes no instance in which the source expressions are defined
-- source:
--   Černý, Czichowsky & Kallsen, Numeraire-invariant quadratic hedging and mean–variance portfolio allocation, arXiv:2110.09416v4, pp. 35, Lemma D.1

import Mathlib
import Definitions.Def_NumInvQH_Oblique_Supplement_Numeraire

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal

namespace NumInvQH.Oblique.Supplement

/-- Weighted rates are defined by the compensator identities (D.8)–(D.11).
In (D.7) the printed V-hat is corrected to its left limit, as on p.36. -/
theorem lemma_D_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (h0 : ∀ A, MeasurableSet[ℱ 0] A → P A = 0 ∨ P A = 1)
    (T : ℝ≥0) {d : ℕ}
    (S : Process Ω (Fin d → ℝ)) (first : Fin d) (hD : AppendixD P ℱ T S first)
    (L V Lh Vh : Process Ω ℝ)
    (hL : ScalarSemi P ℱ T L) (hV : ScalarSemi P ℱ T V)
    (hLh : ScalarSemi (changedMeasure P T (fun t ω => S t ω first)) ℱ T Lh)
    (hVh : ScalarSemi (changedMeasure P T (fun t ω => S t ω first)) ℱ T Vh)
    (hlpos : ∀ᵐ ω ∂P, ∀ t ≤ T, 0 < left L t ω ∧ 0 < left Lh t ω)
    (hlinkL : Same P T L (fun t ω => Lh t ω * densityNumerator P ℱ T
      (fun t ω => S t ω first) t ω / (S t ω first)^2))
    (hlinkV : Same P T V (fun t ω => S t ω first * Vh t ω))
    (A : Clock P ℱ T)
    (Ah : Clock (changedMeasure P T (fun t ω => S t ω first)) ℱ T)
    (hclock : A.value = Ah.value ∧ A.measure = Ah.measure)
    (b bh : Process Ω (Fin d → ℝ))
    (C Ch : Process Ω (Matrix (Fin d) (Fin d) ℝ))
    (u uh : Process Ω (Fin d → ℝ)) (γ γh ℓ ℓh : Process Ω ℝ)
    (hrates : WeightedRates A S L V b C u γ)
    (hhat : WeightedRates Ah (discounted S (fun t ω => S t ω first)) Lh Vh bh Ch uh γh)
    (hℓ : DriftRate A (stochasticLog P ℱ T L) ℓ)
    (hℓh : DriftRate Ah (stochasticLog (changedMeasure P T (fun t ω => S t ω first)) ℱ T Lh) ℓh) :
    let X := fun t ω => S t ω first
    let Sh := discounted S X
    RateAE A (fun t ω =>
      let x := left X t ω
      let s := left S t ω
      let v := left V t ω
      let vh := left Vh t ω
      ℓh t ω = ℓ t ω + 2 / x * b t ω first + (x^2)⁻¹ * C t ω first first ∧
      (∀ i, bh t ω i = (b t ω i + C t ω i first / x -
        s i / x * (b t ω first + C t ω first first / x)) / x) ∧
      (∀ i j, Ch t ω i j = (C t ω i j -
        (s i * C t ω first j + C t ω i first * s j) / x +
        C t ω first first * s i * s j / x^2) / x^2) ∧
      (∀ i, uh t ω i = (u t ω i - (s i * u t ω first + C t ω i first * v) / x +
        C t ω first first * v * s i / x^2) / x^2) ∧
      γh t ω = (γ t ω - 2 * vh * u t ω first + vh^2 * C t ω first first) / x^2 ∧
      (∀ θ : Fin d → ℝ, θ ⬝ᵥ left Sh t ω = -1 →
        θ ⬝ᵥ (Ch t ω *ᵥ θ) - 2 * (θ ⬝ᵥ bh t ω) + ℓh t ω =
          (θ ⬝ᵥ (C t ω *ᵥ θ)) / x^2 - 2 / x * (θ ⬝ᵥ b t ω) + ℓ t ω) ∧
      (∀ θ : Fin d → ℝ, θ ⬝ᵥ left Sh t ω = vh →
        θ ⬝ᵥ (Ch t ω *ᵥ θ) - 2 * (θ ⬝ᵥ uh t ω) + γh t ω =
          (θ ⬝ᵥ (C t ω *ᵥ θ) - 2 * (θ ⬝ᵥ u t ω) + γ t ω) / x^2)) := by sorry

end NumInvQH.Oblique.Supplement
