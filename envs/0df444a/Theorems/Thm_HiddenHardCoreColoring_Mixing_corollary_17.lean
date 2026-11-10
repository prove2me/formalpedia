-- Prove2me | Theorems.Thm_HiddenHardCoreColoring_Mixing_corollary_17
-- name    : HiddenHardCoreColoring.Mixing.corollary_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T09:01:08.319305+00:00
-- url     : https://prove2.me/theorems/434e7d4d-6afe-4ff8-9078-743b6d088119
-- title:
--   Corollary 17 — gap(H_η) ≥ θ*(δ_γ) for every color and background when q ≥ (1+1/e+γ)Δ
-- statement:
--   Let $\theta^*$ be a function with the property of Theorem 5 (for every $\delta\in(0,1)$, $\theta^*(\delta)\in(0,1]$ bounds $\operatorname{gap}(H)$ from below for every $\Delta\ge3$, every graph of maximum degree at most $\Delta$ and all activities in $(0,(1-\delta)\lambda_{\mathrm{crit}}(\Delta)]$). For every $\gamma>0$ put
--   $$\delta_\gamma=\frac{e\gamma/2}{1+e\gamma/2},\qquad\theta_\gamma=\theta^*(\delta_\gamma)\in(0,1].$$
--   If $G$ is a finite simple graph on $n\ge1$ vertices with $\deg(v)\le\Delta$, $q\ge(1+1/e+\gamma)\Delta$ and $\Delta\ge\max\{3,2/\gamma\}$, then
--   $$\operatorname{gap}(H_\eta)\ge\theta_\gamma\qquad\text{for every }c\in[q]\text{ and every }\eta\in\Omega^{-c},$$
--   where $H_\eta$ is the hard-core operator with the hidden activities $\lambda_v(\eta)=1/(|A_v(\eta)|-1)$.
--
--   All hidden models lie uniformly in the uniqueness regime, which is the origin of the threshold $1+1/e$.
--
--   Differences from the source:
--   - reading: θ_γ := θ*(δ_γ), where θ* is the function from Theorem 5 → for every function θs satisfying IsHardCoreGapBound (the conclusion of Theorem 5), θs(δ_γ) ∈ (0,1] and the gap bound holds with θs(δ_γ); reason: Theorem 5 only asserts that such a function exists; the corollary holds for each of them, which specializes to the paper's θ*
--   - encoding: standing assumption q ≥ Δ + 3 → not written; reason: implied by q ≥ (1 + 1/e + γ)Δ and Δ ≥ max{3, 2/γ} (proved in Solutions/verification/HiddenHardCoreColoring_Mixing_Checks.lean); no instance is lost
-- source:
--   Xiongxin Yang, Glauber Dynamics for Sampling Colorings: Rapid Mixing above (1 + 1/e)Δ via Hidden Hard-Core Models, STOC 2027 submission #964 (October 2026), source.pdf sha256 3affe7a3f185d03ac2add85053eb4b8cb6cade88b65c789fb1b595ad6c177146; printed page = PDF page; Corollary 17, p.19

import Mathlib
import Definitions.Def_HiddenHardCoreColoring_Mixing_Hidden

open Finset Matrix

namespace HiddenHardCoreColoring.Mixing

/-- **Corollary 17** (Xiongxin Yang, STOC 2027 submission #964 (October 2026), p.19). Let `θ*` be a function as in Theorem 5, `γ > 0`,
`δ_γ := (eγ/2)/(1 + eγ/2)` and `θ_γ := θ*(δ_γ) ∈ (0, 1]`. If `q ≥ (1 + 1/e + γ)Δ` and `Δ ≥ max{3, 2/γ}`,
then `gap(H_η) ≥ θ_γ` for every color `c` and every background `η ∈ Ω^{-c}`. -/
theorem corollary_17 (θs : ℝ → ℝ) (hθs : IsHardCoreGapBound θs) (γ : ℝ) (hγ : 0 < γ) :
    (0 < θs ((Real.exp 1 * γ / 2) / (1 + Real.exp 1 * γ / 2)) ∧ θs ((Real.exp 1 * γ / 2) / (1 + Real.exp 1 * γ / 2)) ≤ 1) ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (Δ q : ℕ), (∀ v, G.degree v ≤ Δ) → (1 + 1 / Real.exp 1 + γ) * (Δ : ℝ) ≤ (q : ℝ) →
        3 ≤ Δ → 2 / γ ≤ (Δ : ℝ) → ∀ (c : Fin q) (η : Bg G q c),
          θs ((Real.exp 1 * γ / 2) / (1 + Real.exp 1 * γ / 2)) ≤ hcGapH G (hiddenAct G c η) := by sorry

end HiddenHardCoreColoring.Mixing
