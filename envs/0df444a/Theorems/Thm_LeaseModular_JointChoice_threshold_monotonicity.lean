-- Prove2me | Theorems.Thm_LeaseModular_JointChoice_threshold_monotonicity
-- name    : LeaseModular.JointChoice.threshold_monotonicity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:12:23.1938+00:00
-- url     : https://prove2.me/theorems/efc63de4-d1e9-483f-97cc-b8a31b32d8d7
-- title:
--   Proposition 3 (last part), p. 17 — C_M increases in γ; C_SM, C_LM2 increase in δ1, decrease in δ2; C_LM2 decreases in γ
-- statement:
--   Let $0<\delta_2<\delta_1<1$ and $\gamma>0$ with $\gamma\delta_1<1$. Then:
--
--   1. $\gamma\mapsto C_M(\delta_1,\delta_2,\gamma)$ is strictly increasing on $(0,1]$;
--   2. $C_{SM}(\delta_1,\delta_2)$ is strictly increasing in $\delta_1$ on $(\delta_2,1)$ and strictly decreasing in $\delta_2$ on $(0,\delta_1)$;
--   3. $C_{LM2}(\delta_1,\delta_2,\gamma)$ is strictly increasing in $\delta_1$ on $\{\delta_1\in(\delta_2,1):\gamma\delta_1<1\}$ and strictly decreasing in $\delta_2$ on $(0,\delta_1)$;
--   4. $\gamma\mapsto C_{LM2}(\delta_1,\delta_2,\gamma)$ is strictly decreasing where $\gamma>0$ and $\gamma\delta_1<1$.
--
--   These comparative statics say how the regions of Proposition 3 move: better return condition widens the lease-modular region when $\gamma\le1$ and narrows it when $\gamma>1$; a larger durability gap favours modularity.
--
--   **Formalization Note.** $C_{LM2}$ is the corrected threshold. $C_M$ is studied on $\gamma\in(0,1]$, the range in which the paper uses it (its radicand is negative for $\gamma>1$). Each monotonicity is stated on the standing range of the varied parameter with the others fixed.
-- source:
--   Agrawal, Atasu & Ülkü, Leasing, Modularity, and the Circular Economy, author manuscript (Management Science, doi:10.1287/mnsc.2020.3829), Proposition 3, p. 17, last two sentences

import Mathlib
import Definitions.Def_LeaseModular_JointChoice_Setting

namespace LeaseModular.JointChoice

/-- Proposition 3 (last part), p. 17, with `C_LM2` corrected. For `0 < δ₂ < δ₁ < 1` and `γ > 0`
with `γδ₁ < 1`:
1. `C_M(δ₁, δ₂, ·)` is strictly increasing on `γ ∈ (0, 1]`;
2. `C_SM(·, δ₂)` is strictly increasing on `(δ₂, 1)` and `C_SM(δ₁, ·)` strictly decreasing on
   `(0, δ₁)`;
3. `C_LM2(·, δ₂, γ)` is strictly increasing on `{δ₁ ∈ (δ₂, 1) : γδ₁ < 1}` and `C_LM2(δ₁, ·, γ)`
   strictly decreasing on `(0, δ₁)`;
4. `C_LM2(δ₁, δ₂, ·)` is strictly decreasing where `γ > 0` and `γδ₁ < 1`. -/
theorem threshold_monotonicity (δ₁ δ₂ γ : ℝ) (h₂ : 0 < δ₂) (h₂₁ : δ₂ < δ₁) (h₁ : δ₁ < 1)
    (hγ₀ : 0 < γ) (hγ₁ : γ * δ₁ < 1) :
    StrictMonoOn (fun g => CM δ₁ δ₂ g) (Set.Ioc 0 1) ∧
    StrictMonoOn (fun d => CSM d δ₂) (Set.Ioo δ₂ 1) ∧
    StrictAntiOn (fun d => CSM δ₁ d) (Set.Ioo 0 δ₁) ∧
    StrictMonoOn (fun d => CLM2 d δ₂ γ) {d | δ₂ < d ∧ d < 1 ∧ γ * d < 1} ∧
    StrictAntiOn (fun d => CLM2 δ₁ d γ) (Set.Ioo 0 δ₁) ∧
    StrictAntiOn (fun g => CLM2 δ₁ δ₂ g) {g | 0 < g ∧ g * δ₁ < 1} := by sorry

end LeaseModular.JointChoice
