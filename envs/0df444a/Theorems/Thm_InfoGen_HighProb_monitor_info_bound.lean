-- Prove2me | Theorems.Thm_InfoGen_HighProb_monitor_info_bound
-- name    : InfoGen.HighProb.monitor_info_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:28:00.684015+00:00
-- url     : https://prove2.me/theorems/50cfee2f-165e-40f2-bb54-3cf4f33513a1
-- title:
--   Proof of Theorem 3, p. 12, display after (B.5) — the monitor's output satisfies I(Λ_W(S₁),…,Λ_W(S_m);W*,T*,R*) ≤ mε + log(2m)
-- statement:
--   Let $\mathsf W$ be a measurable hypothesis space, $\mu$ a probability measure on $\mathsf Z$, $\ell:\mathsf W\times\mathsf Z\to\mathbb R_+$ a jointly measurable loss, and $P_{W|S}$ a learning algorithm with $I(\Lambda_{\mathsf W}(S);W)\le\varepsilon$, where $\varepsilon\ge0$. Run $m\ge1$ independent copies of $P_{W|S}$ in parallel: $S_t\sim\mu^{\otimes n}$ independent and $W_t$ the output of the $t$-th copy on $S_t$, $t=1,\dots,m$.
--
--   The **monitor** looks at $S^m=(S_1,\dots,S_m)$ and $W^m=(W_1,\dots,W_m)$ and chooses an index $T^*\in[m]$ and a sign $R^*\in\{\pm1\}$ attaining the maximum of $r(L_\mu(W_t)-L_{S_t}(W_t))$, then sets $W^* = W_{T^*}$. Then
--   $$I\big(\Lambda_{\mathsf W}(S_1),\dots,\Lambda_{\mathsf W}(S_m);\, W^*,T^*,R^*\big) \le m\varepsilon + \log(2m).$$
--
--   Given $W^m$, the triple $(W^*,T^*,R^*)$ takes at most $2m$ values. Combined with Lemma B.2, this bounds the expected maximal deviation (B.7).
--
--   **Formalization Note.** The monitor is a Markov kernel from $(S^m, W^m)$ to $[m]\times\{\pm1\}$ constrained to choose an arg max almost surely; ties may be resolved randomly. Here $[m]$ = `Fin m` and $\{\pm1\}$ = `Bool`. Only the final inequality of the display is stated; the conditional mutual information of (B.5) is not formalized. Countability of $\mathsf W$ is unnecessary for this information bound. Joint measurability of $\ell$, $m\ge1$ and $\varepsilon\ge0$ are added.
-- source:
--   Xu & Raginsky, arXiv:1705.07809v2, Proof of Theorem 3, p. 12, display after (B.5) (with (B.3), (B.5) and Lemma B.1)

import Mathlib
import Definitions.Def_InfoGen_HighProb_Setting

open MeasureTheory ProbabilityTheory InformationTheory LearnStability.Characterization
open scoped ENNReal NNReal

namespace InfoGen.HighProb

theorem monitor_info_bound {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    (μ : Measure Z) [IsProbabilityMeasure μ] (n : ℕ)
    (ℓ : W → Z → ℝ) (hℓ : Measurable (Function.uncurry ℓ)) (hℓ0 : ∀ w z, 0 ≤ ℓ w z)
    (κ : Kernel (Fin n → Z) W) [IsMarkovKernel κ]
    (m : ℕ) (hm : 0 < m)
    (ν : Kernel (Fin m → (Fin n → Z) × W) (Fin m × Bool)) [IsMarkovKernel ν]
    (hν : ∀ᵐ q ∂(parallelLaw μ κ m ⊗ₘ ν), ∀ t : Fin m, ∀ r : Bool,
      sgn r * (risk ℓ μ (q.1 t).2 - empRisk ℓ (q.1 t).1 (q.1 t).2) ≤
        sgn q.2.2 * (risk ℓ μ (q.1 q.2.1).2 - empRisk ℓ (q.1 q.2.1).1 (q.1 q.2.1).2))
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε : lambdaInfo ℓ μ κ ≤ ENNReal.ofReal ε) :
    InfoGen.Expected.mutualInfo ((parallelLaw μ κ m ⊗ₘ ν).map
        (fun q => ((fun t => empRiskVec ℓ (q.1 t).1), ((q.1 q.2.1).2, q.2.1, q.2.2)))) ≤
      ENNReal.ofReal (m * ε + Real.log (2 * m)) := by sorry

end InfoGen.HighProb
