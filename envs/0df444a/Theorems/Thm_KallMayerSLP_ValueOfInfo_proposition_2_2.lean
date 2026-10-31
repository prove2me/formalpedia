-- Prove2me | Theorems.Thm_KallMayerSLP_ValueOfInfo_proposition_2_2
-- name    : KallMayerSLP.ValueOfInfo.proposition_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:16:12.354423+00:00
-- url     : https://prove2.me/theorems/961ab8df-e5cb-46f3-9c85-f46094b7d58e
-- title:
--   Proposition 2.2 — $WS\le RS\le EEV$, and $EV\le RS\le EEV$ when only $T(\cdot),h(\cdot)$ are random
-- statement:
--   This is Proposition 2.2 (Madansky) of Kall & Mayer, Chapter 3.
--
--   Let $\xi$ be a random vector in $\mathbb R^r$ with $\xi\in L^2$, and consider the two-stage recourse problem (2.66) with affine random data $T(\xi),W(\xi),h(\xi),q(\xi)$. Let $RS$ be its optimal value, $WS=\mathbb E_\xi[\gamma(\xi)]$ the wait-and-see value, $EV$ the optimal value of the expected value problem, and $EEV$ the expected result of an optimal first-stage solution $\hat x$ of the expected value problem.
--
--   1. For an arbitrary recourse problem (2.66), and every optimal first-stage solution $\hat x$ of the EV problem,
--   $$
--   WS\le RS\le EEV. \tag{2.70}
--   $$
--   2. If only $T(\cdot)$ and $h(\cdot)$ are random ($W$ and $q$ deterministic), then for every such $\hat x$
--   $$
--   EV\le RS\le EEV. \tag{2.71}
--   $$
--
--   The chain (2.70) says that perfect information can only help and that the EV solution can only be worse than the recourse solution; (2.71) shows that, for fixed recourse and costs, the expected value problem gives a lower bound on the recourse problem.
--
--   **Formalization Note** All values are extended reals, and the inequalities hold with no finiteness hypothesis.
--
--   Differences from the source:
--   - encoding: random vector ξ on a probability space (Ω, 𝓕, P) with ξ ∈ L²(Ω, ℝʳ) (Assumption 1.1) → a probability measure μ on ℝʳ (the law ℙ_ξ) whose coordinates are in L²(μ); reason: every quantity of §2.3 depends on ξ only through its law
--   - encoding: min and 𝔼 of values that may be ±∞; 𝔼 undefined for ∞ − ∞ (p.200) → EReal infima; expectation eExp = ∫f⁺ − ∫f⁻, and +∞ when ∫f⁺ = +∞; reason: the book's convention of p.200 (an undefined expected recourse is never chosen); the values agree with the book's wherever the book's are defined
--   - encoding: Q(x; …) := inf over y(·) ∈ Y = L² with a.s. constraints → the LP value realization by realization (secondStageValue at ξ); reason: the book uses Q pointwise (∀ ξ ∈ Ξ in the proof of Prop. 2.2)
--   - encoding: x̂ any optimal first stage solution of (2.67) → ∀ xhat with IsEVOptimal: ∃ ŷ, (xhat, ŷ) feasible for (2.67) with cᵀxhat + q(ξ̄)ᵀŷ = EV; reason: an optimal solution of an LP is a feasible point attaining its value; every such x̂ is covered
--   - encoding: recourse function Q(x; T(ξ), h(ξ)): only T(·), h(·) random → TwoStageSLP.ofRandomTh with deterministic W, q (coefficients Wʲ = 0, qʲ = 0); reason: the book's notation p.200: W(·) ≡ W, q(·) ≡ q
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, Proposition 2.2, eqs. (2.70)–(2.71), p.245 (PDF 254)

import Mathlib
import Definitions.Def_KallMayerSLP_ValueOfInfo_RS
import Definitions.Def_KallMayerSLP_ValueOfInfo_WS
import Definitions.Def_KallMayerSLP_ValueOfInfo_EV
import Definitions.Def_KallMayerSLP_ValueOfInfo_EEV
import Definitions.Def_KallMayerSLP_ValueOfInfo_IsEVOptimal

open MeasureTheory

namespace KallMayerSLP.ValueOfInfo

/-- **Proposition 2.2 (Madansky): `WS ≤ RS ≤ EEV`, and `EV ≤ RS ≤ EEV` when only `T(·)`, `h(·)` are
random.** Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, Proposition 2.2,
eqs. (2.70)–(2.71), p.245 (PDF 254).

Let `μ` be the law of `ξ` on `ℝʳ`, a probability measure with `ξ ∈ L²` (Chapter 3, Assumption 1.1).
1. (2.70) For an arbitrary recourse problem (2.66) with affine random `T(·), W(·), h(·), q(·)`:
   `WS ≤ RS`, and `RS ≤ EEV(x̂)` for every optimal first stage solution `x̂` of the EV problem (2.67).
2. (2.71) With the recourse function `Q(x; T(ξ), h(ξ))` (`W`, `q` deterministic): `EV ≤ RS`, and
   `RS ≤ EEV(x̂)` for every EV-optimal `x̂`.

**Formalization Note.** All values are in `EReal` (see the definitions); the inequalities hold in its
order, with no finiteness hypothesis. -/
theorem proposition_2_2 {r n₁ m₁ n₂ m₂ : ℕ} (μ : Measure (Fin r → ℝ)) [IsProbabilityMeasure μ]
    (hξ : ∀ j, MemLp (fun ξ : Fin r → ℝ => ξ j) 2 μ) :
    (∀ P : TwoStageSLP r n₁ m₁ n₂ m₂,
        WS P μ ≤ RS P μ ∧ ∀ xhat, IsEVOptimal P μ xhat → RS P μ ≤ EEV P μ xhat) ∧
    (∀ (A : Matrix (Fin m₁) (Fin n₁) ℝ) (b : Fin m₁ → ℝ) (c : Fin n₁ → ℝ)
        (T₀ : Matrix (Fin m₂) (Fin n₁) ℝ) (Tc : Fin r → Matrix (Fin m₂) (Fin n₁) ℝ)
        (W : Matrix (Fin m₂) (Fin n₂) ℝ) (h₀ : Fin m₂ → ℝ) (hc : Fin r → Fin m₂ → ℝ)
        (q : Fin n₂ → ℝ),
        let P := TwoStageSLP.ofRandomTh A b c T₀ Tc W h₀ hc q
        EV P μ ≤ RS P μ ∧ ∀ xhat, IsEVOptimal P μ xhat → RS P μ ≤ EEV P μ xhat) := by sorry

end KallMayerSLP.ValueOfInfo
