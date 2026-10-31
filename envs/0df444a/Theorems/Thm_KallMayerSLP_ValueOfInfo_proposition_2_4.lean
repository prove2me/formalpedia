-- Prove2me | Theorems.Thm_KallMayerSLP_ValueOfInfo_proposition_2_4
-- name    : KallMayerSLP.ValueOfInfo.proposition_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:17:00.690131+00:00
-- url     : https://prove2.me/theorems/9a5b5582-1734-4fc2-b787-508fd43b26d8
-- title:
--   Proposition 2.4 — $VSS\le EEV-EV$, and $EVPI\le EEV-EV$ when only $h(\cdot)$ is random
-- statement:
--   This is Proposition 2.4 of Kall & Mayer, Chapter 3; the bounds are due to Birge (for $VSS$) and Avriel–Williams (for $EVPI$).
--
--   Let $\xi$ be a random vector in $\mathbb R^r$ with $\xi\in L^2$, and let $\hat x$ be any optimal first-stage solution of the expected value problem (2.67), at which $EEV$ and $VSS$ are evaluated.
--
--   1. If only the technology matrix $T(\cdot)$ and the right-hand side $h(\cdot)$ are random (recourse function $Q(x;T(\xi),h(\xi))$, with $W$ and $q$ deterministic), the value of the stochastic solution satisfies
--   $$
--   VSS\le EEV-EV. \tag{2.74}
--   $$
--   2. If only the right-hand side $h(\cdot)$ is random (recourse function $Q(x;h(\xi))$), the expected value of perfect information satisfies
--   $$
--   EVPI\le EEV-EV. \tag{2.75}
--   $$
--
--   Both bounds are computable from the expected value problem and one evaluation of the recourse function at its solution, without solving the recourse problem or the wait-and-see problems. Example 2.2 shows that (2.75) fails when $T(\cdot)$ is random.
--
--   **Formalization Note** Values are extended reals and the differences are extended-real subtractions; the inequalities are stated without finiteness hypotheses.
--
--   Differences from the source:
--   - encoding: random vector ξ on a probability space (Ω, 𝓕, P) with ξ ∈ L²(Ω, ℝʳ) (Assumption 1.1) → a probability measure μ on ℝʳ (the law ℙ_ξ) whose coordinates are in L²(μ); reason: every quantity of §2.3 depends on ξ only through its law
--   - encoding: min and 𝔼 of values that may be ±∞; 𝔼 undefined for ∞ − ∞ (p.200) → EReal infima; expectation eExp = ∫f⁺ − ∫f⁻, and +∞ when ∫f⁺ = +∞; reason: the book's convention of p.200 (an undefined expected recourse is never chosen); the values agree with the book's wherever the book's are defined
--   - encoding: Q(x; …) := inf over y(·) ∈ Y = L² with a.s. constraints → the LP value realization by realization (secondStageValue at ξ); reason: the book uses Q pointwise (∀ ξ ∈ Ξ in the proof of Prop. 2.2)
--   - encoding: x̂ any optimal first stage solution of (2.67) → ∀ xhat with IsEVOptimal: ∃ ŷ, (xhat, ŷ) feasible for (2.67) with cᵀxhat + q(ξ̄)ᵀŷ = EV; reason: an optimal solution of an LP is a feasible point attaining its value; every such x̂ is covered
--   - encoding: recourse function Q(x; T(ξ), h(ξ)): only T(·), h(·) random → TwoStageSLP.ofRandomTh with deterministic W, q (coefficients Wʲ = 0, qʲ = 0); reason: the book's notation p.200: W(·) ≡ W, q(·) ≡ q
--   - encoding: recourse function Q(x; h(ξ)): only h(·) random → TwoStageSLP.ofRandomH with deterministic T, W, q; reason: the book's notation p.200: T(·) ≡ T, W(·) ≡ W, q(·) ≡ q
--   - generalization: VSS ≤ EEV − EV and EVPI ≤ EEV − EV for finite values (the differences (2.72)–(2.73) presuppose them) → the same inequalities in EReal with no finiteness hypothesis (Mathlib subtraction, ⊤ − ⊤ = ⊥ in the undefined cases); reason: when RS, WS, EV, EEV are finite the EReal differences are the ordinary ones, so the Lean statement specializes to the book's
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, Proposition 2.4, eqs. (2.74)–(2.75), p.247 (PDF 256)

import Mathlib
import Definitions.Def_KallMayerSLP_ValueOfInfo_EVPI
import Definitions.Def_KallMayerSLP_ValueOfInfo_VSS
import Definitions.Def_KallMayerSLP_ValueOfInfo_IsEVOptimal

open MeasureTheory

namespace KallMayerSLP.ValueOfInfo

/-- **Proposition 2.4 (Birge; Avriel–Williams): `VSS ≤ EEV − EV` and `EVPI ≤ EEV − EV`.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, Proposition 2.4, eqs. (2.74)–(2.75),
p.247 (PDF 256).

Let `μ` be the law of `ξ` on `ℝʳ`, a probability measure with `ξ ∈ L²` (Chapter 3, Assumption 1.1).
1. (2.74) With the recourse function `Q(x; T(ξ), h(ξ))` (only `T(·)`, `h(·)` random; `W`, `q`
   deterministic), for every optimal first stage solution `x̂` of the EV problem (2.67),
   `VSS ≤ EEV − EV`.
2. (2.75) With the recourse function `Q(x; h(ξ))` (only `h(·)` random), for every EV-optimal `x̂`,
   `EVPI ≤ EEV − EV`.

**Formalization Note.** All values are in `EReal` and the differences are `EReal` subtractions. When
the values are finite (the book's case) these are the ordinary differences; the inequalities also hold
in the remaining cases, so no finiteness hypothesis is stated. `EEV` and `VSS` are taken at the same
EV-optimal `x̂`. -/
theorem proposition_2_4 {r n₁ m₁ n₂ m₂ : ℕ} (μ : Measure (Fin r → ℝ)) [IsProbabilityMeasure μ]
    (hξ : ∀ j, MemLp (fun ξ : Fin r → ℝ => ξ j) 2 μ) :
    (∀ (A : Matrix (Fin m₁) (Fin n₁) ℝ) (b : Fin m₁ → ℝ) (c : Fin n₁ → ℝ)
        (T₀ : Matrix (Fin m₂) (Fin n₁) ℝ) (Tc : Fin r → Matrix (Fin m₂) (Fin n₁) ℝ)
        (W : Matrix (Fin m₂) (Fin n₂) ℝ) (h₀ : Fin m₂ → ℝ) (hc : Fin r → Fin m₂ → ℝ)
        (q : Fin n₂ → ℝ),
        let P := TwoStageSLP.ofRandomTh A b c T₀ Tc W h₀ hc q
        ∀ xhat, IsEVOptimal P μ xhat → VSS P μ xhat ≤ EEV P μ xhat - EV P μ) ∧
    (∀ (A : Matrix (Fin m₁) (Fin n₁) ℝ) (b : Fin m₁ → ℝ) (c : Fin n₁ → ℝ)
        (T : Matrix (Fin m₂) (Fin n₁) ℝ) (W : Matrix (Fin m₂) (Fin n₂) ℝ) (h₀ : Fin m₂ → ℝ)
        (hc : Fin r → Fin m₂ → ℝ) (q : Fin n₂ → ℝ),
        let P := TwoStageSLP.ofRandomH A b c T W h₀ hc q
        ∀ xhat, IsEVOptimal P μ xhat → EVPI P μ ≤ EEV P μ xhat - EV P μ) := by sorry

end KallMayerSLP.ValueOfInfo
