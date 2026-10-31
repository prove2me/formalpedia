-- Prove2me | Theorems.Thm_KallMayerSLP_ValueOfInfo_evpi_vss_nonneg
-- name    : KallMayerSLP.ValueOfInfo.evpi_vss_nonneg
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:17:12.061993+00:00
-- url     : https://prove2.me/theorems/6e78b61c-c06d-4f2b-a31d-be2af9dcf9c2
-- title:
--   §2.3, p.246 — $EVPI\ge 0$ and $VSS\ge 0$
-- statement:
--   For an arbitrary two-stage recourse problem (2.66) with $\xi\in L^2$:
--
--   1. the expected value of perfect information is nonnegative,
--   $$
--   EVPI=RS-WS\ge0,
--   $$
--   2. for every optimal first-stage solution $\hat x$ of the expected value problem, the value of the stochastic solution is nonnegative,
--   $$
--   VSS=EEV-RS\ge0,
--   $$
--
--   each whenever the difference is defined, i.e. not of the form $\infty-\infty$.
--
--   The book obtains both from Proposition 2.2.
--
--   Differences from the source:
--   - encoding: random vector ξ on a probability space (Ω, 𝓕, P) with ξ ∈ L²(Ω, ℝʳ) (Assumption 1.1) → a probability measure μ on ℝʳ (the law ℙ_ξ) whose coordinates are in L²(μ); reason: every quantity of §2.3 depends on ξ only through its law
--   - encoding: min and 𝔼 of values that may be ±∞; 𝔼 undefined for ∞ − ∞ (p.200) → EReal infima; expectation eExp = ∫f⁺ − ∫f⁻, and +∞ when ∫f⁺ = +∞; reason: the book's convention of p.200 (an undefined expected recourse is never chosen); the values agree with the book's wherever the book's are defined
--   - encoding: Q(x; …) := inf over y(·) ∈ Y = L² with a.s. constraints → the LP value realization by realization (secondStageValue at ξ); reason: the book uses Q pointwise (∀ ξ ∈ Ξ in the proof of Prop. 2.2)
--   - encoding: x̂ any optimal first stage solution of (2.67) → ∀ xhat with IsEVOptimal: ∃ ŷ, (xhat, ŷ) feasible for (2.67) with cᵀxhat + q(ξ̄)ᵀŷ = EV; reason: an optimal solution of an LP is a feasible point attaining its value; every such x̂ is covered
--   - encoding: EVPI = RS − WS and VSS = EEV − RS, used where defined → hypotheses excluding the forms +∞ − (+∞) and −∞ − (−∞); reason: a nondegeneracy condition that only excludes the undefined differences
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, §2.3, p.246 (PDF 255): 'Obviously due to Prop. 2.2 we have EVPI ≥ 0. […] Also in this case Prop. 2.2 implies VSS ≥ 0.'

import Mathlib
import Definitions.Def_KallMayerSLP_ValueOfInfo_EVPI
import Definitions.Def_KallMayerSLP_ValueOfInfo_VSS
import Definitions.Def_KallMayerSLP_ValueOfInfo_IsEVOptimal

open MeasureTheory

namespace KallMayerSLP.ValueOfInfo

/-- **`EVPI ≥ 0` and `VSS ≥ 0`.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, §2.3, p.246 (PDF 255): "Obviously due
to Prop. 2.2 we have `EVPI ≥ 0`. […] Also in this case Prop. 2.2 implies `VSS ≥ 0`."

For an arbitrary recourse problem (2.66) with law `μ` of `ξ ∈ L²`:
1. if `EVPI = RS − WS` is defined (not of the form `+∞ − (+∞)` or `−∞ − (−∞)`), then `EVPI ≥ 0`;
2. for every EV-optimal `x̂`, if `VSS = EEV(x̂) − RS` is defined, then `VSS ≥ 0`.

**Formalization Note.** The book's differences are taken where they are defined; the hypotheses
exclude exactly the two forms `∞ − ∞` (Mathlib's `EReal` would return `⊥` there). -/
theorem evpi_vss_nonneg {r n₁ m₁ n₂ m₂ : ℕ} (μ : Measure (Fin r → ℝ)) [IsProbabilityMeasure μ]
    (hξ : ∀ j, MemLp (fun ξ : Fin r → ℝ => ξ j) 2 μ) (P : TwoStageSLP r n₁ m₁ n₂ m₂) :
    ((¬ (RS P μ = ⊤ ∧ WS P μ = ⊤) ∧ ¬ (RS P μ = ⊥ ∧ WS P μ = ⊥)) → 0 ≤ EVPI P μ) ∧
    (∀ xhat, IsEVOptimal P μ xhat →
      (¬ (EEV P μ xhat = ⊤ ∧ RS P μ = ⊤) ∧ ¬ (EEV P μ xhat = ⊥ ∧ RS P μ = ⊥)) →
        0 ≤ VSS P μ xhat) := by sorry

end KallMayerSLP.ValueOfInfo
