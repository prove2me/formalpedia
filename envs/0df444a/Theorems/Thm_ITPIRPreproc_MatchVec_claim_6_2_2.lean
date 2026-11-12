-- Prove2me | Theorems.Thm_ITPIRPreproc_MatchVec_claim_6_2_2
-- name    : ITPIRPreproc.MatchVec.claim_6_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:12:18.594195+00:00
-- url     : https://prove2.me/theorems/6b092106-98fe-4280-8b72-989450400de8
-- title:
--   Claim 6.2.2 — the activation-bit query is uniform on $\mathcal R^+$
-- statement:
--   Let $m=2^h$ with $h\ge3$, and let $u_a,v_a\in\mathbb Z_6^d$ satisfy (7) with the vectors $v_a\bmod2$ pairwise distinct. For every target $i=(a^\star,b^\star)\in[m]\times\mathbb F_2^h$, if $(R,\rho)\leftarrow\mathcal R^+_i$ is uniform and $(Q,u)\leftarrow\mathsf{Query}(i,(R,\rho))$, that is, $Q=(R+\delta u_{a^\star}^T,\ \rho+\gamma u_{a^\star})$ for independent uniform $\gamma\in\mathbb F_2$, $\delta\in\mathbb F_2^h$, then
--   $$Q\equiv\mathrm{Unif}(\mathcal R^+).$$
--
--   This is property (ii) of Definition 4.1 for the activation-bit primitive: the query the server sees carries no information about the target.
--
--   Differences from the source:
--   - encoding: (R, ρ) ← R⁺_i, (Q, u) ← Query(i, (R, ρ)) ⟹ Q ≡ Unif(R⁺) → for every Q₀, the average over R⁺_i of Pr[Q = Q₀] equals 1/|R⁺|; reason: the law of Q under the uniform key of R⁺_i, pointwise on a finite set; same statement
-- source:
--   Jesko Dujmovic, Zhengnan Lai, Daniel Wichs, Nearly Optimal Information-Theoretic PIR with Client Preprocessing, STOC 2027 submission #572 (October 2026), Claim 6.2.2, printed p.22 (PDF p.24)

import Mathlib
import Definitions.Def_ITPIRPreproc_MatchVec_ActivationPrimitive

open scoped ENNReal

namespace ITPIRPreproc.MatchVec

/-- Claim 6.2.2, printed p.22 (PDF p.24). For every target `i = (a⋆, b⋆)`, if `(R, ρ) ← R⁺_i`
and `(Q, u) ← Query(i, (R, ρ))`, the query `Q = (Q, ρ̃)` is uniform on `R⁺`. -/
theorem claim_6_2_2 (h d : ℕ) (u v : Fin (2 ^ h) → Fin d → ZMod 6) (hh : 3 ≤ h)
    (hmv : IsMVFamily (2 ^ h) d u v) :
    ∀ (i : Pos h) (Q₀ : ActKey h d),
      avgOver (actCompat v i) (fun K => (actQuery u i K).toOuterMeasure {p | p.1 = Q₀}) =
        (Fintype.card (ActKey h d) : ℝ≥0∞)⁻¹ := by sorry

end ITPIRPreproc.MatchVec
