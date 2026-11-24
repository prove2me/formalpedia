-- Prove2me | Theorems.Thm_MirrorBP_JEA_Supplement_theorem_2
-- name    : MirrorBP.JEA.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T02:48:41.720561+00:00
-- url     : https://prove2.me/theorems/9f14c7a4-3197-452e-ac6d-9262a5504ebe
-- title:
--   Theorem 2, pp. 22–23 — finite-buffer MBP with (24) loses at most Cm(K/T + √(ηK)) + M₂/K, M₂ = C√m (d̄_Σ/min{d̄_Σ−1,1})^{3/2}/d̄_min
-- statement:
--   Let $V$ be a set of $m=|V|>1$ nodes, $V_b\subseteq V$ a set of buffer-constrained nodes with scaled buffer sizes $\bar d_j\in(0,1)$ for $j\in V_b$ ($\bar d_j=1$ otherwise) and $\bar d_\Sigma=\sum_{j\in V}\bar d_j>1$. Let the demand types $\tau\in\mathcal T$ have nonempty pick-up and drop-off neighbourhoods $P(\tau),D(\tau)\subseteq V$ and payoffs $|w_{j\tau k}|\le1$. Let $(\varphi^t)_{t<T}$ be probability vectors on $\mathcal T$ satisfying Condition 1 ($\alpha(\varphi^t)>0$) and varying $\eta$-slowly (Definition 1), and $\alpha_{\min}=\min_t\alpha(\varphi^t)$.
--
--   There are a universal constant $C<\infty$ and a threshold $K_1=c(m+1/\alpha_{\min}+1/\bar d_{\min}+1/\bar d_g)^N$ ($c,N$ universal; $\bar d_{\min}=\min_j\bar d_j$, $\bar d_g=\min\{1,\bar d_\Sigma-1\}$) such that, for every $K\ge K_1$ with whole-number buffer sizes $d_j=\bar d_jK$, Algorithm 1 run with the congestion function (24) and the normalization (23), under any tie-breaking, satisfies
--   $$L^{\rm MBP}_T\le M_1\Big(\frac KT+\sqrt{\eta K}\Big)+M_2\frac1K,\qquad M_1=Cm,\quad M_2=C\,\frac1{\min_{j\in V}\bar d_j}\left(\frac{\sum_{j\in V}\bar d_j}{\min\{\sum_{j\in V}\bar d_j-1,1\}}\right)^{3/2}\sqrt m .$$
--   Here $L^{\rm MBP}_T=W^*_T-W^{\rm MBP}_T$ compares the best feasible (buffer-respecting) policy from its best initial state with MBP from its worst initial state over the periods $0,\dots,T-1$.
--
--   This extends Theorem 1 to queues with finite buffers; for $V_b=\emptyset$ it gives back the $Cm^2/K$ term of Theorem 1.
--
--   **Formalization Note** The loss is stated without suprema: for every buffer-respecting policy $\pi$ and initial states $q,q'$, $(J(\pi,q,T)-J(\mathrm{MBP},q',T))/T$ is at most the bound. The constants $C,c,N$ are quantified before the instance.
--
--   Differences from the source:
--   - reading: K₁ = poly(m, d̄, 1/α_min) → K₁ = c·(m + 1/α_min + 1/d̄_min + 1/d̄_g)^N with universal c, N, d̄_min = min_j d̄_j, d̄_g = min{1, ∑_j d̄_j − 1}; reason: the thresholds derived in Appendix B.3.3 (PDF 44–45) are polynomial in m, 1/α, 1/d̄_min, 1/d̄_g, and d̄_Σ ≤ m; a polynomial in the bounded entries d̄_j alone cannot express the blow-up as d̄_min or d̄_g tends to 0
--   - generalization: Condition 1 for (φᵗ)_{t≤T} and α_min = min_{0≤t≤T} α(φᵗ) → Condition 1 for the T periods t = 0, …, T − 1 and α_min = min_{t<T} α(φᵗ); reason: the T periods are 0, …, T − 1 (as in the published base model); φ^T never enters the dynamics, and dropping it can only enlarge α_min, so every source instance is covered with a no larger threshold
--   - reading: Algorithm 1: serve iff the score is nonnegative and q_{j*} > 0 → in the finite-buffer setting also require that the drop-off buffer has room (q_{k*} + 1 ≤ d_{k*} unless j* = k*); the argmax is over all of P(τ) × D(τ) and is not re-optimized; reason: a feasible policy of §5.1 cannot overflow a buffer; the boundary indicator in (41) counts both empty and full queues
--   - reading: buffer size d_j = d̄_j K (p. 21), with d̄_j ≜ d_j/K (p. 22) → hypothesis IntegralCapacity: every d̄_j K is a natural number; reason: a buffer size is a number of supply units; the model with K units exists exactly for these K, and 'q_j = d_j' (a full buffer) is then an exact equality
--   - generalization: max_{τ,j∈P(τ),k∈D(τ)} |w_{jτk}| = 1 (p. 10) → |w_{jτk}| ≤ 1 on P(τ) × D(τ); reason: the scaling is stated without loss of generality; every instance of the source satisfies the Lean hypothesis
--   - generalization: policies map the history of types and states to decisions (p. 10) → the benchmark policies also observe their own past decisions (published base policy class); reason: the class contains every policy of the source, so the benchmark only grows
--   - encoding: L_T = W*_T − W_T^MBP with sup over policies and max/min over initial states (4), (6) → for every feasible policy π and all initial states q, q′: (J(π, q, T) − J(MBP, q′, T))/T ≤ bound; reason: equivalent to the bound on the sup/max minus the min
-- source:
--   Kanoria, Qian, Blind Dynamic Resource Allocation in Closed Networks via Mirror Backpressure, arXiv:1903.02764v4, pp. 22–23, §5.1, Theorem 2; (23), (24); Appendix B.3.3 (PDF 44–45) for the threshold

import Mathlib
import Definitions.Def_MirrorBP_JEA_Model
import Definitions.Def_MirrorBP_JEA_MBP
import Definitions.Def_MirrorBP_JEA_Supplement_Buffer
import Definitions.Def_MirrorBP_JEA_Supplement_Growth

namespace MirrorBP.JEA.Supplement

open Finset

theorem theorem_2 :
    ∃ C : ℝ, ∃ c : ℝ, ∃ N : ℕ,
      ∀ (V Ty : Type) [Fintype V] [DecidableEq V] [Fintype Ty] [DecidableEq Ty]
        (P D : Ty → Finset V) (w : V → Ty → V → ℝ) (phi : ℕ → Ty → ℝ) (T : ℕ) (eta : ℝ) (K : ℕ)
        (Vb : Finset V) (dbar : V → ℝ) (sel : (V → ℕ) → Ty → V × V),
        1 < Fintype.card V → (∀ τ, (P τ).Nonempty) → (∀ τ, (D τ).Nonempty) →
        (∀ τ, ∀ j ∈ P τ, ∀ k ∈ D τ, |w j τ k| ≤ 1) →
        0 < T → (∀ t < T, IsRate (phi t)) → (∀ t < T, 0 < alphaConn P D (phi t)) →
        VariesSlowly phi T eta →
        IsBufferProfile Vb dbar → IntegralCapacity dbar K →
        c * ((Fintype.card V : ℝ) + 1 / alphaMin P D phi T + 1 / dMin dbar + 1 / dGap dbar) ^ N
          ≤ (K : ℝ) →
        ∀ hsel : IsArgmaxSelB P D w (congestion24 Vb dbar K) dbar K sel,
        ∀ π : Policy P D, RespectsBuffers dbar K π →
        ∀ q ∈ BufStateSpace dbar K, ∀ q' ∈ BufStateSpace dbar K,
          (expPayoff w phi π T q
              - expPayoff w phi (mbpPolicyB P D w (congestion24 Vb dbar K) dbar K sel hsel.mem) T q') / T
            ≤ C * (Fintype.card V : ℝ) * ((K : ℝ) / T + Real.sqrt (eta * K))
              + C * (1 / dMin dbar) * (dSum dbar / min (dSum dbar - 1) 1) ^ ((3 : ℝ) / 2)
                  * Real.sqrt (Fintype.card V) / K := by sorry

end MirrorBP.JEA.Supplement
