-- Prove2me | Theorems.Thm_KallMayerSLP_ValueOfInfo_evpi_vss_zero_of_deterministic
-- name    : KallMayerSLP.ValueOfInfo.evpi_vss_zero_of_deterministic
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:16:51.976695+00:00
-- url     : https://prove2.me/theorems/2b5b8fc3-dd11-46b1-b975-f5f4ee69a5d7
-- title:
--   §2.3, p.246 — no randomness gives $EVPI=VSS=0$
-- statement:
--   Suppose there is no randomness: for some fixed $\hat\xi\in\mathbb R^r$, $\mathbb P_\xi(\xi=\hat\xi)=1$. Then for an arbitrary two-stage recourse problem (2.66):
--
--   1. $EVPI=RS-WS=0$, whenever this difference is defined (here $RS=WS$, so whenever $RS$ is finite);
--   2. $VSS=EEV-RS=0$ for every optimal first-stage solution $\hat x$ of the expected value problem.
--
--   Conversely, a strictly positive $EVPI$ or $VSS$ is evidence of genuine randomness, which is how these values are used as a "measure of the degree of stochasticity".
--
--   Differences from the source:
--   - encoding: random vector ξ with ℙ_ξ(ξ = ξ̂) = 1 → a probability measure μ on ℝʳ with μ{ξ̂} = 1; ξ ∈ L² not assumed separately; reason: the quantities depend only on the law, and μ{ξ̂} = 1 implies ξ ∈ L²
--   - encoding: min and 𝔼 of values that may be ±∞; 𝔼 undefined for ∞ − ∞ (p.200) → EReal infima; expectation eExp = ∫f⁺ − ∫f⁻, and +∞ when ∫f⁺ = +∞; reason: the book's convention of p.200 (an undefined expected recourse is never chosen); the values agree with the book's wherever the book's are defined
--   - encoding: Q(x; …) := inf over y(·) ∈ Y = L² with a.s. constraints → the LP value realization by realization (secondStageValue at ξ); reason: the book uses Q pointwise (∀ ξ ∈ Ξ in the proof of Prop. 2.2)
--   - encoding: x̂ any optimal first stage solution of (2.67) → ∀ xhat with IsEVOptimal: ∃ ŷ, (xhat, ŷ) feasible for (2.67) with cᵀxhat + q(ξ̄)ᵀŷ = EV; reason: an optimal solution of an LP is a feasible point attaining its value; every such x̂ is covered
--   - encoding: EVPI = RS − WS and VSS = EEV − RS, used where defined → hypotheses excluding the forms +∞ − (+∞) and −∞ − (−∞); reason: a nondegeneracy condition that only excludes the undefined differences
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, §2.3, p.246 (PDF 255): 'if with some fixed ξ̂ ∈ ℝʳ we have ℙ_ξ(ξ = ξ̂) = 1, then obviously follows EVPI = VSS = 0'

import Mathlib
import Definitions.Def_KallMayerSLP_ValueOfInfo_EVPI
import Definitions.Def_KallMayerSLP_ValueOfInfo_VSS
import Definitions.Def_KallMayerSLP_ValueOfInfo_IsEVOptimal

open MeasureTheory

namespace KallMayerSLP.ValueOfInfo

/-- **No randomness: `EVPI = VSS = 0`.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, §2.3, p.246 (PDF 255): "If in the
problem at hand there is no randomness around, in other words if with some fixed `ξ̂ ∈ ℝʳ` we have
`ℙ_ξ(ξ = ξ̂) = 1`, then obviously follows `EVPI = VSS = 0`."

For an arbitrary recourse problem (2.66) whose law `μ` satisfies `μ{ξ̂} = 1`:
1. if `EVPI = RS − WS` is defined (not `∞ − ∞`), then `EVPI = 0`;
2. `VSS = EEV(x̂) − RS = 0` for every EV-optimal `x̂`.

**Formalization Note.** `ξ ∈ L²` is not assumed separately: it follows from `μ{ξ̂} = 1`. In this
case `RS = WS`, so `EVPI` is defined exactly when `RS` is finite; `VSS` needs no such hypothesis,
since an EV-optimal `x̂` makes all values finite. -/
theorem evpi_vss_zero_of_deterministic {r n₁ m₁ n₂ m₂ : ℕ} (μ : Measure (Fin r → ℝ))
    [IsProbabilityMeasure μ] (ξhat : Fin r → ℝ) (hdet : μ {ξhat} = 1)
    (P : TwoStageSLP r n₁ m₁ n₂ m₂) :
    ((¬ (RS P μ = ⊤ ∧ WS P μ = ⊤) ∧ ¬ (RS P μ = ⊥ ∧ WS P μ = ⊥)) → EVPI P μ = 0) ∧
    (∀ xhat, IsEVOptimal P μ xhat → VSS P μ xhat = 0) := by sorry

end KallMayerSLP.ValueOfInfo
