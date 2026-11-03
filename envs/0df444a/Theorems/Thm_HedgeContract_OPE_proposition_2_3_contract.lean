-- Prove2me | Theorems.Thm_HedgeContract_OPE_proposition_2_3_contract
-- name    : HedgeContract.OPE.proposition_2_3_contract
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-03T04:06:43.219411+00:00
-- url     : https://prove2.me/theorems/bde24f98-6efd-4129-b5a5-147aad90eb5a
-- title:
--   Proposition 2.3 (contract part), pp. 36–39 — the reflected feedback contract attains the value
-- statement:
--   Assume the standing model bounds and all six parts of Assumption 6.2. Let $W$ be the principal's control value, that is, for every $y\ge0$, $W(y)$ is the least upper bound of the payoffs of admissible contracts started from promise $y$. Let $\bar y=\sup\{y\ge0: W(y)<\widetilde W(y)\}$, where $\widetilde W(y)=\mu-ry+\sup_{(Z,\zeta)\in\mathcal Z\times\Gamma}(A^*(Z)-g(Z,\zeta))$.
--
--   Suppose in addition that $W$ has the properties established in Proposition 6.4:
--
--   1. the set defining $\bar y$ is bounded above;
--   2. $W\in C^2(0,\infty)$;
--   3. $\delta W(y)=\sup_{(Z,\zeta)\in\mathcal Z\times\Gamma}\{\delta(\mu+A^*(Z))+(ry+g(Z,\zeta))W'(y)+\tfrac12\Sigma(Z,\zeta)W''(y)\}$ for $0<y<\bar y$;
--   4. $W'(y)=-\delta$ for $y\ge\bar y$;
--   5. $W(0)=\delta\Phi$ and $W''(\bar y)=0$;
--   6. $W$ is concave on $[0,\infty)$ and strictly concave on $[0,\bar y)$.
--
--   Then there are selectors $Z^*,\zeta^*$ such that, for every $y\in(0,\bar y]$, the pair $(Z^*(y),\zeta^*(y))$ maximizes
--
--   $$\delta A^*(Z)+g(Z,\zeta)W'(y)+\tfrac12\Sigma(Z,\zeta)W''(y)\quad\text{over }(Z,\zeta)\in\mathcal Z\times\Gamma,$$
--
--   and for every initial promise $\hat y\ge0$ there is an admissible contract $(Z,\zeta,I)$ with state $Y$ whose payoff equals $W(\hat y)$ and which, almost surely,
--
--   1. pays the lump sum $I_0=(\hat y-\bar y)^+$ at time zero;
--   2. keeps $Y_t\in[0,\bar y]$ for all $t<\tau$, where $\tau=\inf\{t\ge0:Y_t\le0\}$;
--   3. makes its later payments only when $Y_t=\bar y$ (the payment measure gives no mass to $\{0<t\le\tau: Y_t<\bar y\}$);
--   4. liquidates exactly when $Y$ hits zero: $Y_\tau=0$ when $\tau<\infty$;
--   5. uses the feedback controls $Z_t=Z^*(Y_t)$, $\zeta_t=\zeta^*(Y_t)$ for Lebesgue-almost every $t<\tau$.
--
--   This is the second half of the proof of Proposition 2.3: once Proposition 6.4 identifies the value as a concave $C^2$ solution of the free-boundary problem, the maximizing feedback controls (Lemma 6.5, Corollary 6.6) generate a contract reflected at the payment boundary $\bar y$ that attains the value. Together with Proposition 6.4 it yields Proposition 2.3.
--
--   **Formalization Note.** The hypotheses are exactly the conclusions of `HedgeContract.OPE.proposition_6_4`; the conclusion is exactly the contract clause of `HedgeContract.OPE.proposition_2_3`. Model objects ($A^*$, $g$, $\Sigma$, the payment measure, admissibility) are those of `Definitions.Def_HedgeContract_OPE_Model`.
-- source:
--   Huang, Ju & Xing, Optimal Contracting with Unobservable Managerial Hedging, working paper (Nov. 14, 2017), Proposition 2.3, p. 13 (PDF 15); proof in §6.6, pp. 36–39 (PDF 38–41): definition of (Z*(y), ζ*(y)) on p. 36, eq. (61), Lemma 6.5, U* and Corollary 6.6, and the verification step completing the proof of Proposition 2.3, taking Proposition 6.4 (p. 35) as given

import Mathlib
import Definitions.Def_HedgeContract_OPE_Model
set_option autoImplicit false

namespace HedgeContract.OPE
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

/-- Proposition 2.3, contract part: given the conclusions of Proposition 6.4, the reflected
feedback contract (Lemma 6.5, Corollary 6.6) is admissible and attains the control value. -/
theorem proposition_2_3_contract (P : Params) (hP : P.Standing) (h62 : Assumption62 P)
    {Ω : Type*} [MeasurableSpace Ω] (P₀ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P₀]
    (B : ℝ≥0 → Ω → Fin 2 → ℝ) (hB : Peng1990.SMP.IsStdBrownian P₀ B)
    (W : ℝ → ℝ) (hW : IsValue P P₀ B hB W)
    (hbdd : BddAbove {y : ℝ | 0 ≤ y ∧ W y < Wtil P y})
    (hC2 : ContDiffOn ℝ 2 W (Set.Ioi 0))
    (hHJB : ∀ y ∈ Set.Ioo 0 (ybar P W),
      P.δ * W y = hamSup P y (deriv W y) (deriv (deriv W) y))
    (hslope : ∀ y : ℝ, 0 ≤ y → ybar P W ≤ y →
      HasDerivWithinAt W (-P.δ) (Set.Ici 0) y)
    (hW0 : W 0 = P.δ * P.Φ)
    (hW2 : derivWithin (derivWithin W (Set.Ici 0)) (Set.Ici 0) (ybar P W) = 0)
    (hconc : ConcaveOn ℝ (Set.Ici 0) W)
    (hsconc : StrictConcaveOn ℝ (Set.Ico 0 (ybar P W)) W) :
    ∃ Zs ζs : ℝ → ℝ,
      (∀ y ∈ Set.Ioc 0 (ybar P W),
        IsMaximizer P (deriv W y) (deriv (deriv W) y) (Zs y) (ζs y)) ∧
      ∀ yhat : ℝ, 0 ≤ yhat → ∃ C : Contract Ω,
      C.Admissible P P₀ B hB yhat ∧
      C.payoff P P₀ = W yhat ∧
      (∀ᵐ ω ∂P₀,
        C.I 0 ω = max (yhat - ybar P W) 0 ∧
        (∀ t : ℝ≥0, (t : ℝ≥0∞) < C.τ ω → C.Y t ω ∈ Set.Icc 0 (ybar P W)) ∧
        C.paymentMeasure ω
          {t : ℝ | 0 < t ∧ ENNReal.ofReal t ≤ C.τ ω ∧
            C.Y t.toNNReal ω < ybar P W} = 0 ∧
        (C.τ ω < ⊤ → C.Y (C.τ ω).toReal.toNNReal ω = 0) ∧
        (∀ᵐ t : ℝ ∂MeasureTheory.volume,
          0 ≤ t → ENNReal.ofReal t < C.τ ω →
          C.Z t.toNNReal ω = Zs (C.Y t.toNNReal ω) ∧
          C.ζ t.toNNReal ω = ζs (C.Y t.toNNReal ω))) := by sorry

end HedgeContract.OPE
