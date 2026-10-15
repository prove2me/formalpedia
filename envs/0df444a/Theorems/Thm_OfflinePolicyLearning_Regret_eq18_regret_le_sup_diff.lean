-- Prove2me | Theorems.Thm_OfflinePolicyLearning_Regret_eq18_regret_le_sup_diff
-- name    : OfflinePolicyLearning.Regret.eq18_regret_le_sup_diff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:33:52.325974+00:00
-- url     : https://prove2.me/theorems/3823ef36-0a3f-44ab-823d-1a93acb89116
-- title:
--   (18), p. 22 — the regret of an empirical maximizer is at most sup_{π₁,π₂∈Π} |Δ̂(π₁,π₂) − Δ(π₁,π₂)|
-- statement:
--   Work in the potential-outcome model of the mission with bounded rewards ($|Y(a)|\le B$ almost surely given every $x$). Fix a sample $D$ of size $n$, cross-fitted estimators, a policy class $\Pi$, and a policy $\hat\pi\in\Pi$ that maximizes $\hat Q_{CAIPWL}$ over $\Pi$ on $D$. Then
--   $$R(\hat\pi)\le\sup_{\pi_1,\pi_2\in\Pi}\big|\hat\Delta(\pi_1,\pi_2)-\Delta(\pi_1,\pi_2)\big|.$$
--
--   This deterministic reduction turns the regret bound into uniform control of $\hat\Delta-\Delta$, which the triangle inequality splits into $\hat\Delta-\tilde\Delta$ (Lemma 3) and $\tilde\Delta-\Delta$ (oracle concentration).
--
--   **Formalization Note** The regret is $\sup_{\pi'\in\Pi}Q(\pi')-Q(\hat\pi)$ (no maximizer $\pi^*$ is assumed). Bounded rewards make $|Q|\le B$, so both suprema are suprema of bounded families ($\hat\Delta$ takes finitely many values on a fixed sample).
-- source:
--   Zhou, Athey & Wager, Offline Multi-Action Policy Learning, arXiv:1810.04778v2, p. 22, Remark 8, display (18), up to the first supremum

import Mathlib
import Definitions.Def_OfflinePolicyLearning_Regret_Hamming
import Definitions.Def_OfflinePolicyLearning_Regret_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace OfflinePolicyLearning.Regret
theorem eq18_regret_le_sup_diff {X : Type*} [MeasurableSpace X] {d K n : ℕ}
    (M : Model X d) (B : ℝ) (hB : ∀ x, ∀ᵐ y ∂(M.κY x), ∀ a, |y a| ≤ B)
    (C : CrossFit X d K) (Pol : Set (X → Fin d)) (D : Fin n → Draw X d)
    (πh : X → Fin d) (hmem : πh ∈ Pol) (hmax : ∀ π ∈ Pol, C.Qhat D π ≤ C.Qhat D πh) :
    M.regret Pol πh ≤ ⨆ π₁ : Pol, ⨆ π₂ : Pol, |C.Δhat D π₁.1 π₂.1 - M.Δ π₁.1 π₂.1| := by sorry
end OfflinePolicyLearning.Regret
