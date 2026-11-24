-- Prove2me | Theorems.Thm_MirrorBP_JEA_Supplement_theorem_4
-- name    : MirrorBP.JEA.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T02:50:24.559802+00:00
-- url     : https://prove2.me/theorems/5a50a6d0-5d53-4ea9-8f6f-4bbd059e7416
-- title:
--   Theorem 4, Appendix D, appendix p. 14 (corrected: K > K₁) — any congestion family satisfying Condition 3 loses at most (4√(M₁m)+2M₁)(K/T+√(ηK)) + M₂/K
-- statement:
--   Let $V$ be a set of $m=|V|>1$ nodes, $V_b\subseteq V$ a set of buffer-constrained nodes with scaled buffer sizes $\bar d_j\in(0,1)$ for $j\in V_b$ ($\bar d_j=1$ otherwise) and $\sum_{j\in V}\bar d_j>1$. Let the demand types have nonempty neighbourhoods $P(\tau),D(\tau)$ and payoffs $|w_{j\tau k}|\le1$, let $T\ge1$, and let $(\varphi^t)_{t<T}$ be probability vectors with $\alpha(\varphi^t,P,D)>0$ (Condition 1) varying $\eta$-slowly for some $\eta\in[0,2]$, with $\alpha_{\min}=\min_t\alpha(\varphi^t)$.
--
--   Let $(f_j)_{j\in V}$ be any congestion functions (a family indexed by the number of units $K$) satisfying Condition 3 with parameters $(\alpha_{\min},K_1,M_1,M_2)\in\mathbb R^4_{++}$. Then for every $K>K_1$ with whole-number buffer sizes $\bar d_jK$, Algorithm 1 run with $(f_j)$ and the normalization (23), under any tie-breaking, satisfies
--   $$L^{\rm MBP}_T\le\big(4\sqrt{M_1m}+2M_1\big)\Big(\frac KT+\sqrt{\eta K}\Big)+M_2\frac1K .$$
--
--   Theorem 4 is the general finite-buffer guarantee: Theorem 2 follows by Lemma 9, and the bound is explicit in the growth parameters.
--
--   **Formalization Note** The paper states the bound for $K\ge K_1$ while Condition 3 constrains the congestion functions only for $K>K_1$; at $K=K_1$ the family is unconstrained and the bound can fail (see the correction below). The loss is stated without suprema (every buffer-respecting policy $\pi$, all initial states $q,q'$).
--
--   Differences from the source:
--   - correction: for any K ≥ K₁ → for any K > K₁; reason: Condition 3 constrains the family only for K > K₁, so at K = K₁ ∈ ℕ the functions are arbitrary: take a family satisfying Condition 3 (e.g. (24) by Lemma 9, with K₁ a large natural number) and replace its member at K = K₁ by f ≡ 0; with m = 2, types τ₁ (P = {a, b}, D = {b}, w_{aτ₁b} = 1, w_{bτ₁b} = 1/2) and τ₂ (P = {b}, D = {a}, w = −1/2), φ = (1/2, 1/2), MBP at K = K₁ always selects (a, b) for τ₁ and drops τ₂, so it earns at most K/T on average while serving τ₁ by the self-pair (b, b) earns 1/4; for T → ∞ the loss tends to 1/4 > M₂/K₁ (DISPROOF.md)
--   - reading: Condition 3 prints 'for any K > K₁' only in 1(a) and 2(a), takes 2(b) over q, q′ ∈ Ω and B(f) ⊆ Ω → every clause of Condition 3 is required for every K > K₁, over the normalized physical states, with the windows [q̄_j ± 1/K̃] inside (0, d̄_j); reason: (24) depends on K and fails 2(c), 2(d) for small K; the appendix verifies 2(b) as a sup over Ω_K; the window clause only excludes families for which the maxima of f_j′ in (43) and 2(c) are undefined
--   - generalization: Condition 1 for (φᵗ)_{t≤T} and α_min = min_{0≤t≤T} α(φᵗ) → Condition 1 for the T periods t = 0, …, T − 1 and α_min = min_{t<T} α(φᵗ); reason: the T periods are 0, …, T − 1 (as in the published base model); φ^T never enters the dynamics, and dropping it can only enlarge α_min, so every source instance is covered with a no larger threshold
--   - reading: Algorithm 1: serve iff the score is nonnegative and q_{j*} > 0 → in the finite-buffer setting also require that the drop-off buffer has room (q_{k*} + 1 ≤ d_{k*} unless j* = k*); the argmax is over all of P(τ) × D(τ) and is not re-optimized; reason: a feasible policy of §5.1 cannot overflow a buffer; the boundary indicator in (41) counts both empty and full queues
--   - reading: buffer size d_j = d̄_j K (p. 21), with d̄_j ≜ d_j/K (p. 22) → hypothesis IntegralCapacity: every d̄_j K is a natural number; reason: a buffer size is a number of supply units; the model with K units exists exactly for these K, and 'q_j = d_j' (a full buffer) is then an exact equality
--   - generalization: max_{τ,j∈P(τ),k∈D(τ)} |w_{jτk}| = 1 (p. 10) → |w_{jτk}| ≤ 1 on P(τ) × D(τ); reason: the scaling is stated without loss of generality; every instance of the source satisfies the Lean hypothesis
--   - generalization: policies map the history of types and states to decisions (p. 10) → the benchmark policies also observe their own past decisions (published base policy class); reason: the class contains every policy of the source, so the benchmark only grows
--   - encoding: L_T = W*_T − W_T^MBP with sup over policies and max/min over initial states (4), (6) → for every feasible policy π and all initial states q, q′: (J(π, q, T) − J(MBP, q′, T))/T ≤ bound; reason: equivalent to the bound on the sup/max minus the min
-- source:
--   Kanoria, Qian, Blind Dynamic Resource Allocation in Closed Networks via Mirror Backpressure, arXiv:1903.02764v4, Appendix D, appendix p. 14 (PDF 47), Theorem 4; Condition 3, Appendix B.3.1, appendix pp. 8–9 (PDF 41–42)

import Mathlib
import Definitions.Def_MirrorBP_JEA_Model
import Definitions.Def_MirrorBP_JEA_MBP
import Definitions.Def_MirrorBP_JEA_Supplement_Buffer
import Definitions.Def_MirrorBP_JEA_Supplement_Growth

namespace MirrorBP.JEA.Supplement

open Finset

theorem theorem_4 {V Ty : Type} [Fintype V] [DecidableEq V] [Fintype Ty] [DecidableEq Ty]
    (P D : Ty → Finset V) (w : V → Ty → V → ℝ) (Vb : Finset V) (dbar : V → ℝ)
    (f : ℕ → V → ℝ → ℝ) (K₁ M₁ M₂ : ℝ) (phi : ℕ → Ty → ℝ) (T : ℕ) (eta : ℝ) (K : ℕ)
    (sel : (V → ℕ) → Ty → V × V)
    (hm : 1 < Fintype.card V) (hP : ∀ τ, (P τ).Nonempty) (hD : ∀ τ, (D τ).Nonempty)
    (hw : ∀ τ, ∀ j ∈ P τ, ∀ k ∈ D τ, |w j τ k| ≤ 1)
    (hbuf : IsBufferProfile Vb dbar)
    (hT : 0 < T) (hrate : ∀ t < T, IsRate (phi t)) (hconn : ∀ t < T, 0 < alphaConn P D (phi t))
    (hcond : Condition3 Vb dbar f (alphaMin P D phi T) K₁ M₁ M₂)
    (heta : 0 ≤ eta ∧ eta ≤ 2) (hslow : VariesSlowly phi T eta)
    (hK : K₁ < (K : ℝ)) (hcap : IntegralCapacity dbar K)
    (hsel : IsArgmaxSelB P D w (f K) dbar K sel) :
    ∀ π : Policy P D, RespectsBuffers dbar K π →
    ∀ q ∈ BufStateSpace dbar K, ∀ q' ∈ BufStateSpace dbar K,
      (expPayoff w phi π T q - expPayoff w phi (mbpPolicyB P D w (f K) dbar K sel hsel.mem) T q') / T
        ≤ (4 * Real.sqrt (M₁ * Fintype.card V) + 2 * M₁) * ((K : ℝ) / T + Real.sqrt (eta * K))
          + M₂ / K := by sorry

end MirrorBP.JEA.Supplement
