-- Prove2me | Theorems.Thm_MirrorBP_JEA_Supplement_theorem_3
-- name    : MirrorBP.JEA.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T02:49:50.450481+00:00
-- url     : https://prove2.me/theorems/e6bb2619-f891-4bb3-a4d8-d6155552c341
-- title:
--   Theorem 3, p. 25 — MBP for joint pricing-assignment (Algorithm 2) loses at most CmK/T + Cm²/K, and at most Cm²/K in the infinite horizon
-- statement:
--   Consider the joint pricing-assignment setting of §5.2: a set $V$ of $m=|V|>1$ nodes, demand types $\tau\in\mathcal T$ with nonempty neighbourhoods $P(\tau),D(\tau)$, a stationary type distribution $\varphi$ with $(\varphi,P,D)$ satisfying Condition 1 ($\alpha(\varphi,P,D)>0$), price intervals $[p^{\min}_\tau,p^{\max}_\tau]$, costs $c_{j\tau k}$ with $\max_\tau p^{\max}_\tau+\max_{j,k,\tau}|c_{j\tau k}|=1$, and willingness-to-pay distribution functions $(F_\tau)$ satisfying Condition 2.
--
--   There is a universal constant $C>0$ such that for every such instance there is $K_1<\infty$ with the following property. For every $K\ge K_1$, Algorithm 2 run with the congestion function (8) and the normalization (9), under any choice of the two argmaxes, satisfies for every horizon $T\ge1$
--   $$L^{\rm MBP}_T\le Cm\,\frac KT+Cm^2\,\frac1K,$$
--   and, in the infinite horizon,
--   $$L^{\rm MBP}=W^*-W^{\rm MBP}\le Cm^2\,\frac1K,$$
--   where $W^*=\limsup_TW^*_T$ and $W^{\rm MBP}=\liminf_TW^{\rm MBP}_T$.
--
--   So the blind pricing-and-assignment policy, which does not know $\varphi$, is within $O(K/T+1/K)$ per customer of the optimal control.
--
--   **Formalization Note** $C$ is chosen before the instance and $K_1$ after it, as in the statement. The finite-horizon loss is stated without suprema (every admissible control $\pi$, all initial states $q,q'$). The infinite-horizon clause uses $W^*$ and $W^{\rm MBP}$ as defined in `MirrorBP.JEA.Supplement.JPA`.
--
--   Differences from the source:
--   - reading: Algorithm 2 posts p_τ[t] ← F_τ^{-1}(μ_τ[t]) → the posted price is p_τ(μ_τ) = F_τ^{-1}(1 − μ_τ), which realizes the fraction μ_τ; reason: p. 24 defines μ_τ as the realized fraction and calls p_τ(μ_τ) the inverse of the willingness-to-pay distribution; Algorithm 2's F_τ^{-1} denotes that inverse
--   - reading: Algorithm 2's update q̄[t+1] = q̄[t] − (1/K̃) x_{j*τk*}[t](e_{j*} − e_{k*}) → the unit moves (and p − c is earned) only when the customer buys; reason: item (2), p. 23, and the algorithm's own comment 'if the incoming demand stays, serve it'
--   - encoding: randomized controls with continuum prices → controls randomize over finitely supported (decision, price) distributions; reason: contains every deterministic history-dependent control; deterministic controls attain each finite-horizon optimum (compact prices, continuous payoffs), so W*_T and W* are unchanged
--   - encoding: Condition 2 parts (1)–(2) and the inverse p_τ(μ) (p. 24) → F_τ monotone, continuous, 0 below p_τ^min, 1 above p_τ^max, positive derivative inside; p_τ(μ) = sup{p ∈ [p_τ^min, p_τ^max] : F_τ(p) ≤ 1 − μ}; reason: these are the properties the source derives from Condition 2; the sup is the inverse for such F_τ
--   - encoding: L_T^MBP = W*_T − W_T^MBP (6) → for every admissible control π and initial states q, q′: (J(π, q, T) − J(MBP, q′, T))/T ≤ bound; reason: equivalent to the bound on the sup/max minus the min
--   - generalization: policies map the history of types and states to decisions (p. 10) → the benchmark policies also observe their own past decisions (published base policy class); reason: the class contains every policy of the source, so the benchmark only grows
-- source:
--   Kanoria, Qian, Blind Dynamic Resource Allocation in Closed Networks via Mirror Backpressure, arXiv:1903.02764v4, p. 25, Theorem 3 and Algorithm 2; pp. 23–24, Condition 2; p. 10, (4)–(6)

import Mathlib
import Definitions.Def_MirrorBP_JEA_Model
import Definitions.Def_MirrorBP_JEA_MBP
import Definitions.Def_MirrorBP_JEA_SPP
import Definitions.Def_MirrorBP_JEA_Supplement_JPA

namespace MirrorBP.JEA.Supplement

open Finset

theorem theorem_3 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (V Ty : Type) [Fintype V] [DecidableEq V] [Fintype Ty] [DecidableEq Ty]
        (P D : Ty → Finset V) (phi : Ty → ℝ) (c : V → Ty → V → ℝ) (pmin pmax : Ty → ℝ)
        (F : Ty → ℝ → ℝ),
        1 < Fintype.card V → (∀ τ, (P τ).Nonempty) → (∀ τ, (D τ).Nonempty) →
        IsRate phi → 0 < alphaConn P D phi →
        Condition2 pmin pmax F → JPANormalized pmax c →
        ∃ K₁ : ℝ, ∀ K : ℕ, K₁ ≤ (K : ℝ) →
          ∀ (sel : (V → ℕ) → Ty → V × V) (muSel : (V → ℕ) → Ty → ℝ),
          IsArgmaxPairJ P D c (fMBP (Fintype.card V)) K sel →
          IsArgmaxMuJ F pmin pmax c (fMBP (Fintype.card V)) K sel muSel →
            (∀ T : ℕ, 0 < T → ∀ π : JPolicy V Ty, AdmissibleJ P D pmin pmax π →
              ∀ q ∈ StateSpace V K, ∀ q' ∈ StateSpace V K,
                (expPayoffJ c F phi π T q
                    - expPayoffJ c F phi (mbpPolicyJ F pmin pmax sel muSel) T q') / T
                  ≤ C * (Fintype.card V : ℝ) * K / T + C * (Fintype.card V : ℝ) ^ 2 / K) ∧
            WstarJ P D pmin pmax c F phi K - WpiJ c F phi (mbpPolicyJ F pmin pmax sel muSel) K
              ≤ C * (Fintype.card V : ℝ) ^ 2 / K := by sorry

end MirrorBP.JEA.Supplement
