-- Prove2me | Theorems.Thm_InfoRelaxTS_Monotone_Ukn_interpolation
-- name    : InfoRelaxTS.Monotone.Ukn_interpolation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T23:31:21.419475+00:00
-- url     : https://prove2.me/theorems/1c79735c-84f1-4ab3-bf0e-68e36c0512fb
-- title:
--   (154)–(155), §D.3.2, p. 59 — U_{k,n} ≥ U_{k,n+1}, with W^IRS.FH = U_{1,0}, W^IRS.V-Zero = U_{K,T}, U_{k+1,0} = U_{k,T}
-- statement:
--   The model is the Bayesian bandit of §2.1: arms $a \in \mathcal A = \{1,\dots,K\}$ (0-based in Lean, $K \ge 1$), reward laws $\mathcal R_a(\theta_a)$, conjugate priors $\mathcal P_a(y_a)$, the Bayesian update $\mathcal U_a$, and the outcome law $\mathcal I(y)$ under which the arms are independent, $\theta_a \sim \mathcal P_a(y_a)$, and the rewards of arm $a$ are i.i.d. $\mathcal R_a(\theta_a)$ given $\theta_a$. The standing assumptions of §2.1 hold: $\mathcal U_a(y_a,r)$ is the Bayes posterior after observing $r$, the update maps are measurable, and $\mathbb E_{y_a}|R_{a,1}| < \infty$ for every belief $y_a$ (3).
--
--   Fix a horizon $T$ and a belief vector $y$, and let $U_{k,n}$ ($k \in \mathcal A$, $0 \le n \le T$) be the quantities (154): the expected best allocation of $T$ pulls when arms $a < k$ earn their actual cumulative payoffs $S_a(n_a)$, arm $k$ earns $S_k$ on its first $n$ pulls and $\hat\mu_{k,T-1}$ on each further pull, and arms $a > k$ earn $\hat\mu_{a,T-1}$ per pull. Then
--
--   $$U_{k,n} \ge U_{k,n+1} \qquad \forall k = 1,\dots,K,\ \forall n = 0,\dots,T-1, \tag{155}$$
--
--   and
--
--   $$W^{IRS.FH}(T,y) = U_{1,0}, \qquad W^{IRS.V\text{-}Zero}(T,y) = U_{K,T}, \qquad U_{k+1,0} = U_{k,T} \ (k < K).$$
--
--   Chaining these gives $W^{IRS.FH}(T,y) \ge W^{IRS.V\text{-}Zero}(T,y)$, the second inequality of (57).
--
--   **Formalization Note** Arms are 0-based, so the paper's $U_{1,0}$ is `Ukn 0 0` and $U_{K,T}$ is `Ukn (K-1) T`. The page prints the coefficient of $(n_k - n)^+$ as $\hat\mu_{a,T-1}$; it is $\hat\mu_{k,T-1}$ (cf. (158)).
-- source:
--   Min, Maglaras, Moallemi, Thompson Sampling with Information Relaxation Penalties, arXiv:1902.04251v2, p. 59, §D.3.2, (154)–(155)

import Mathlib
import Definitions.Def_InfoRelaxTS_Monotone_Setting

namespace InfoRelaxTS.Monotone

open MeasureTheory ProbabilityTheory

/-- (154)–(155), §D.3.2, p. 59: `U_{k,n} ≥ U_{k,n+1}` for every arm `k` and every `n < T`, together
with the three identities observed there: `W^{IRS.FH} = U_{1,0}`, `W^{IRS.V-Zero} = U_{K,T}` and
`U_{k+1,0} = U_{k,T}` (arms 0-based). -/
theorem Ukn_interpolation {K : ℕ} [NeZero K] {Θ Y : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ]
    [Nonempty Θ] [MeasurableSpace Y]
    (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin K → Kernel Y Θ) [∀ a, IsMarkovKernel (P a)]
    (U : Fin K → Y → ℝ → Y) (hM : StandingAssumptions R P U)
    (T : ℕ) (y : Fin K → Y) :
    (∀ (k : Fin K) (n : ℕ), n < T → Ukn R P U k (n + 1) T y ≤ Ukn R P U k n T y) ∧
      WFH R P U T y = Ukn R P U 0 0 T y ∧
      WVZ R P U T y = Ukn R P U ⟨K - 1, Nat.sub_one_lt (NeZero.ne K)⟩ T T y ∧
      ∀ (k : Fin K) (hk : (k : ℕ) + 1 < K), Ukn R P U ⟨(k : ℕ) + 1, hk⟩ 0 T y = Ukn R P U k T T y := by sorry

end InfoRelaxTS.Monotone
