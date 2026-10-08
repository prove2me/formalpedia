-- Prove2me | Theorems.Thm_MFGLimit_Conc_theorem_5_3
-- name    : MFGLimit.Conc.theorem_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:25:25.544675+00:00
-- url     : https://prove2.me/theorems/1e0bc28a-570f-489c-b46d-8db124f000d3
-- title:
--   Theorem 5.3, p. 19 — dimension-uniform transport inequality for an SDE path law
-- statement:
--   Fix $T>0$, a spatial Lipschitz bound $L$, and an upper bound $S$ on the operator norm of the diffusion matrix. A constant $\kappa>0$ depending only on $(T,L,S)$ works in every positive pair of dimensions $k,k'$. For a jointly measurable drift $b:[0,T]\times\mathbb R^k\to\mathbb R^k$ with $L$-Lipschitz spatial sections and bounded $b(t,0)$, let $P_x$ be the law of the solution of $dX_t=b(t,X_t)dt+\sigma dW_t$, $X_0=x$, with $\|\sigma\|_{\rm op}\le S$. For every $Q\in\mathcal P_1(C^k)$ absolutely continuous with respect to $P_x$,
--   $$W_{1,(C^k,\|\cdot\|_{k,2})}(Q,P_x)\le\sqrt{2\kappa R(Q\mid P_x)}.$$
--   Consequently every 1-Lipschitz $\Phi$ on this path space satisfies $P_x(\Phi-\langle P_x,\Phi\rangle>a)\le\exp(-a^2/(2\kappa))$ for $a>0$.
--
--   This is the dimension-uniform SDE transport input to Theorem 5.4.
--
--   **Formalization Note** The path norm is the $\ell^2$ norm of coordinatewise sup norms, as specified by (5.1), and the SDE solution is supplied as a path-valued process.
-- source:
--   Delarue, Lacker & Ramanan, From the master equation to mean field game limit theory: large deviations and concentration of measure, arXiv:1804.08550v1, p. 19, Theorem 5.3, (5.2)–(5.3)

import Mathlib
import Definitions.Def_MFGLimit_Conc_Transport

namespace MFGLimit.Conc

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- Theorem 5.3: the coordinate-sup-norm path law of a Lipschitz SDE satisfies a
dimension-independent `T₁` inequality and its concentration consequence. -/
theorem theorem_5_3 (T : ℝ≥0) (hT : 0 < T) (L S : ℝ) (hL : 0 ≤ L) (hS : 0 ≤ S) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ (k k' : ℕ), 1 ≤ k → 1 ≤ k' →
      ∀ (Ω : Type) [mΩ : MeasurableSpace Ω],
      ∀ (P : Measure Ω), IsProbabilityMeasure P →
      ∀ (𝔽 : Filtration ℝ≥0 mΩ)
        (W : ℝ≥0 → Ω → Fin k' → ℝ), IsFWiener 𝔽 P W →
      ∀ (b : ℝ≥0 → E k → E k),
        Measurable (fun q : {q : ℝ≥0 × E k // q.1 ≤ T} => b q.1.1 q.1.2) →
        (∀ t ≤ T, ∀ x y, ‖b t x - b t y‖ ≤ L * ‖x - y‖) →
        (∃ K : ℝ, ∀ t ≤ T, ‖b t 0‖ ≤ K) →
      ∀ (σ : Matrix (Fin k) (Fin k') ℝ), matrixOpNorm σ ≤ S →
      ∀ (Xx : E k → Ω → Path k T),
        (∀ x, IsSingleSDE P 𝔽 T W b σ x (Xx x)) →
      ∀ x : E k,
        let Px : Measure (CoordPaths k T) :=
          P.map (fun ω => toCoordPaths (Xx x ω))
        IsPp 1 Px ∧
        (∀ Q : Measure (CoordPaths k T), IsPp 1 Q → Q ≪ Px →
          WassersteinDRO.Duality.wassersteinDistance 1 Q Px ≤
            (ENNReal.ofReal (2 * κ) * InformationTheory.klDiv Q Px) ^ (1 / 2 : ℝ)) ∧
        (∀ a : ℝ, 0 < a → ∀ Φ : CoordPaths k T → ℝ,
          LipschitzWith 1 Φ → Integrable Φ Px ∧
          Px {z | Φ z - ∫ y, Φ y ∂Px > a} ≤
            ENNReal.ofReal (Real.exp (-(a ^ 2) / (2 * κ)))) := by sorry

end MFGLimit.Conc
