-- Prove2me | Theorems.Thm_MirrorBP_JEA_Supplement_proposition_5
-- name    : MirrorBP.JEA.Supplement.proposition_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T02:49:14.093276+00:00
-- url     : https://prove2.me/theorems/f705137a-244a-4a67-ad76-9f73688ab935
-- title:
--   Proposition 5, Appendix E.1, appendix p. 16 — in the JPA setting W*_T ≤ W^SPP + mK/T and W* ≤ W^SPP
-- statement:
--   Consider the joint pricing-assignment setting of §5.2: $m=|V|>1$ nodes, demand types with nonempty neighbourhoods $P(\tau),D(\tau)$, a stationary type distribution $\varphi$, price intervals $[p^{\min}_\tau,p^{\max}_\tau]$, costs $c_{j\tau k}$ and willingness-to-pay distribution functions $F_\tau$ satisfying Condition 2 and the scaling $\max_\tau p^{\max}_\tau+\max_{j,k,\tau}|c_{j\tau k}|=1$. Let $W^{\rm SPP}$ be the optimal value of the static planning problem (49)–(51).
--
--   For every number of supply units $K$, every horizon $T\ge1$, every admissible pricing-assignment control $\pi$ and every initial state $q[0]\in\Omega_K$,
--   $$\frac1T\sum_{t=0}^{T-1}\mathbb E\big[v^\pi[t]\mid q[0]\big]\le W^{\rm SPP}+\frac{mK}T,$$
--   so $W^*_T\le W^{\rm SPP}+mK/T$; and the infinite-horizon optimum satisfies
--   $$W^*=\limsup_{T\to\infty}W^*_T\le W^{\rm SPP}.$$
--
--   This is the benchmark half of the analysis of Algorithm 2: it bounds what any control can earn by the concave static planning value.
--
--   **Formalization Note** The finite-horizon clause is stated for every control and initial state, which is the bound on $W^*_T$. Admissible controls randomize over finitely many (decision, price) pairs; this class contains all deterministic history-dependent controls.
--
--   Differences from the source:
--   - encoding: randomized controls (p. 10, 'we allow x to be randomized'; prices are a continuum) → controls randomize over finitely supported (decision, price) distributions; reason: the class contains every deterministic history-dependent control; with compact price sets and continuous payoffs a deterministic control attains each finite-horizon optimum, so W*_T is the same; this avoids integrals over price laws, whose Lean value is 0 when not integrable
--   - encoding: Condition 2 parts (1)–(2) and the inverse p_τ(μ) (p. 24) → F_τ monotone, continuous, 0 below p_τ^min, 1 above p_τ^max, positive derivative inside; p_τ(μ) = sup{p ∈ [p_τ^min, p_τ^max] : F_τ(p) ≤ 1 − μ}; reason: these are the properties the source derives from Condition 2; the sup is the inverse for such F_τ
-- source:
--   Kanoria, Qian, Blind Dynamic Resource Allocation in Closed Networks via Mirror Backpressure, arXiv:1903.02764v4, Appendix E.1, appendix p. 16 (PDF 49), Proposition 5 and (49)–(51)

import Mathlib
import Definitions.Def_MirrorBP_JEA_Model
import Definitions.Def_MirrorBP_JEA_SPP
import Definitions.Def_MirrorBP_JEA_Supplement_JPA

namespace MirrorBP.JEA.Supplement

open Finset

theorem proposition_5 {V Ty : Type} [Fintype V] [DecidableEq V] [Fintype Ty] [DecidableEq Ty]
    (P D : Ty → Finset V) (phi : Ty → ℝ) (c : V → Ty → V → ℝ) (pmin pmax : Ty → ℝ)
    (F : Ty → ℝ → ℝ)
    (hm : 1 < Fintype.card V) (hP : ∀ τ, (P τ).Nonempty) (hD : ∀ τ, (D τ).Nonempty)
    (hrate : IsRate phi) (hcond2 : Condition2 pmin pmax F) (hnorm : JPANormalized pmax c)
    (K : ℕ) :
    (∀ T : ℕ, 0 < T → ∀ π : JPolicy V Ty, AdmissibleJ P D pmin pmax π → ∀ q ∈ StateSpace V K,
        expPayoffJ c F phi π T q / T
          ≤ WsppJ P D F pmin pmax c phi + (Fintype.card V : ℝ) * K / T) ∧
      WstarJ P D pmin pmax c F phi K ≤ WsppJ P D F pmin pmax c phi := by sorry

end MirrorBP.JEA.Supplement
