-- Prove2me | Theorems.Thm_GinibrePermanent977_Anticoncentration_Supplement_theorem_4_1
-- name    : GinibrePermanent977.Anticoncentration.Supplement.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:38:08.464206+00:00
-- url     : https://prove2.me/theorems/ea05715b-4b23-4f78-b748-016f84650191
-- title:
--   Theorem 4.1 — Gaussian perturbation comparison
-- statement:
--   Let $\mathbb K\in\{\mathbb R,\mathbb C,\mathbb H\}$, $\beta=\dim_{\mathbb R}\mathbb K$, and $n\ge1$. Let $Z$ be an arbitrary random $n\times n$ matrix, independent of the standard Ginibre matrix $G$. There is a constant $C_\beta>0$, fixed before $n$ and the law of $Z$, for which all the following hold. For every $w\in\mathbb K$ and $s\ge0$,
--   $$(30)\qquad E e^{-s|\operatorname{per}_{\mathbb K}(Z+G)-w|^2}\le E e^{-s|\operatorname{per}_{\mathbb K}G|^2}.$$
--   Let $p_n$ be the radial density of the normalized Gaussian permanent from Theorem 1.1. The normalized perturbed permanent has a Lebesgue density $q$ with
--   $$(31)\qquad \|q\|_\infty\le p_n(0)\le\kappa_{n,\beta}.$$
--   For every $\varepsilon>0$ and every center $w$,
--   $$P(|\operatorname{per}_{\mathbb K}(Z+G)-w|\le\varepsilon\sqrt{n!})\le\min\{1,\omega_\beta p_n(0)\varepsilon^\beta\}\le\min\{1,\omega_\beta\kappa_{n,\beta}\varepsilon^\beta\},$$
--   and
--   $$(32)\qquad P(|\operatorname{per}_{\mathbb K}(Z+G)-w|\le\varepsilon\sqrt{n!})\le C_\beta\min\{1,n^{(\beta+2)/4}\varepsilon^\beta\}.$$
--   Here $\omega_\beta=\pi^{\beta/2}/\Gamma(\beta/2+1)$ is the Euclidean unit-ball volume and $\kappa_{n,\beta}$ is (22). In the complex case the exact last bound with $\kappa$ is $\min\{1,n\varepsilon^2\}$. The Gaussian density satisfies $\|p_n\|_\infty=p_n(0)$, $p_n(z)\le p_n(0)$ and $p_n(0)\le C_\beta n^{(\beta+2)/4}$, and is chosen before the law of $Z$. This gives arbitrary independent perturbations the same density bound as the Gaussian model. No entry independence, boundedness, mean or moment assumption is made on $Z$.
--
--   **Formalization Note** Both densities are nonnegative extended-real measurable functions; their infinity norms are Lebesgue essential suprema. Probability bounds are measure inequalities in the nonnegative extended reals.
--
--   Differences from the source:
--
--   - encoding: K ∈ {ℝ,ℂ,ℍ} and β = dim_ℝ K → published Scalar carriers and beta; reason: the three concrete fields and real-coordinate normalizations are identical
--   - encoding: independent random inputs → coordinate functions under their probability product laws; reason: these are exactly the joint laws of independent Borel random variables; no moment or density restriction is added
--   - encoding: the density p_n from Theorem 1.1 and an infinity norm → an existential Gaussian density with its radial, essential-supremum, pointwise maximum and finite upper bounds; essSup q volume ≤ p 0; reason: the Gaussian witness is selected before every perturbation law; its maximum at zero is intrinsic to the continuous radial Gaussian-mixture density
--   - encoding: the implicit constant and supremum over centers → one C > 0 per Scalar before n and perturbation laws; inequalities for every center; reason: constants may be enlarged to their maximum; pointwise bounds express the uniform supremum
--   - generalization: Theorem 4.1 displays the polynomial small-ball estimate (32) → also the exact min{1,ω_β p_n(0) ε^β} ≤ min{1,ω_β κ_n,β ε^β} bound; reason: integration of (31) over the ball in the proof, p.14, gives this bound; dropping it recovers (30)–(32)
-- source:
--   Frederic Koehler, Pui Kuen Leung, STOC 2027 submission #977 (October 2026), Theorem 4.1, p.14 (PDF SHA256 e25737f1d5e3492905f8eeaa41d92c55d95f73622a3b5846cc87aac6a346d4ec)

import Mathlib
import Definitions.Def_GinibrePermanent977_Anticoncentration_Supplement_Model
open MeasureTheory ProbabilityTheory
open scoped Nat ENNReal

namespace GinibrePermanent977.Anticoncentration.Supplement

/-- Theorem 4.1 (30)–(32), p.14. One Gaussian density p and one polynomial constant C are
chosen before the arbitrary perturbation law. The same p(0) controls every perturbation q.
The ball bounds retain the exact volume constants from the proof. -/
theorem theorem_4_1 (F : Scalar) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∃ p : F.K → ℝ≥0∞,
      IsDensity (ginibre F n n) normPer p ∧
      (∀ z w : F.K, ‖z‖ = ‖w‖ → p z = p w) ∧
      essSup p volume = p 0 ∧ (∀ z, p z ≤ p 0) ∧
      p 0 ≤ ENNReal.ofReal (kappa F n) ∧
      p 0 ≤ ENNReal.ofReal (C * (n : ℝ) ^ (((F.beta : ℝ) + 2) / 4)) ∧
      ∀ (μ : Measure (Fin n → Fin n → F.K)), IsProbabilityMeasure μ →
        (∀ (w : F.K) (s : ℝ), 0 ≤ s →
          (∫ ZG, Real.exp (-s * ‖perK (ZG.1 + ZG.2) - w‖ ^ 2)
            ∂(μ.prod (ginibre F n n))) ≤
          ∫ G, Real.exp (-s * ‖perK G‖ ^ 2) ∂ginibre F n n) ∧
        ∃ q : F.K → ℝ≥0∞,
          IsDensity (μ.prod (ginibre F n n)) perturbedPer q ∧
          essSup q volume ≤ p 0 ∧
          ∀ ε : ℝ, 0 < ε → ∀ w : F.K,
            (μ.prod (ginibre F n n))
              {ZG | ‖perK (ZG.1 + ZG.2) - w‖ ≤ ε * Real.sqrt (n ! : ℝ)} ≤
                min 1 (ENNReal.ofReal (omegaBall F * ε ^ F.beta) * p 0) ∧
            min 1 (ENNReal.ofReal (omegaBall F * ε ^ F.beta) * p 0) ≤
                ENNReal.ofReal (min 1 (omegaBall F * kappa F n * ε ^ F.beta)) ∧
            (μ.prod (ginibre F n n))
              {ZG | ‖perK (ZG.1 + ZG.2) - w‖ ≤ ε * Real.sqrt (n ! : ℝ)} ≤
                ENNReal.ofReal (C * min 1 ((n : ℝ) ^ (((F.beta : ℝ) + 2) / 4) *
                  ε ^ F.beta)) := by sorry

end GinibrePermanent977.Anticoncentration.Supplement
