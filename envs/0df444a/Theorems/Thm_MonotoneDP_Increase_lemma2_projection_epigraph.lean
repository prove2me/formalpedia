-- Prove2me | Theorems.Thm_MonotoneDP_Increase_lemma2_projection_epigraph
-- name    : MonotoneDP.Increase.lemma2_projection_epigraph
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:00:02.911375+00:00
-- url     : https://prove2.me/theorems/40e29054-aa4b-4f65-8269-39fad404c6fb
-- title:
--   Lemma 2 — P(C_k) ⊂ closure of P(C_k) = E[T^k(J̄)], with equality iff the infimum defining T^k(J̄) is attained
-- statement:
--   Let $(S,C,U,H,\bar J)$ be a monotone model satisfying Assumption I, and let $E(\cdot)$, $C_k$, $P(\cdot)$ and $\overline{\,\cdot\,}$ be the epigraph, the sets (55), the projection (56) and the closure in $\lambda$ (57). Then for every $k\ge1$:
--
--   1. $$P(C_k)\subseteq\overline{P(C_k)}=E[T^k(\bar J)];$$
--   2. $$P(C_k)=\overline{P(C_k)}=E[T^k(\bar J)]$$
--   holds if and only if, for each $x\in S$, the infimum in
--   $$T^k(\bar J)(x)=\inf_{u\in U(x)}H[x,u,T^{k-1}(\bar J)]$$
--   is attained, i.e. there is $u\in U(x)$ with $H[x,u,T^{k-1}(\bar J)]=\inf_{v\in U(x)}H[x,v,T^{k-1}(\bar J)]$.
--
--   The lemma identifies the epigraph of each value iterate with a projection of the set $C_k$, which is the device the paper uses to relate convergence of the dynamic programming algorithm to interchanging projection and intersection.
--
--   **Formalization Note** Attainment is required at every $x$, including states where the infimum is $+\infty$ (where every $u\in U(x)$ attains it).
-- source:
--   Bertsekas, Monotone Mappings with Application in Dynamic Programming, SIAM J. Control Optim. 15 (1977), p. 457 (PDF p. 20), Lemma 2, eqs. (58)–(60). DOI 10.1137/0315031

import Mathlib
import Definitions.Def_MonotoneDP_Increase_Model
import Definitions.Def_MonotoneDP_Increase_Assumptions
import Definitions.Def_MonotoneDP_Increase_Epigraph

namespace MonotoneDP.Increase

/-- Bertsekas (1977), p. 457, Lemma 2: under Assumption I, for all `k ≥ 1`,
`P(C_k) ⊆ \overline{P(C_k)} = E[T^k(J̄)]` (eq. (58)); and
`P(C_k) = \overline{P(C_k)} = E[T^k(J̄)]` (eq. (59)) holds iff for each `x ∈ S` the infimum
`T^k(J̄)(x) = inf_{u ∈ U(x)} H[x, u, T^{k−1}(J̄)]` (eq. (60)) is attained. -/
theorem lemma2_projection_epigraph {S C : Type*} (m : Model S C) (hI : m.AssumptionI) :
    ∀ k : ℕ, 1 ≤ k →
      (m.P (m.Ck k) ⊆ Pbar (m.P (m.Ck k)) ∧
        Pbar (m.P (m.Ck k)) = E ((m.T)^[k] m.Jbar)) ∧
      ((m.P (m.Ck k) = Pbar (m.P (m.Ck k)) ∧
          Pbar (m.P (m.Ck k)) = E ((m.T)^[k] m.Jbar)) ↔
        ∀ x : S, ∃ u ∈ m.U x,
          m.H x u ((m.T)^[k - 1] m.Jbar) =
            ⨅ v ∈ m.U x, m.H x v ((m.T)^[k - 1] m.Jbar)) := by sorry

end MonotoneDP.Increase
