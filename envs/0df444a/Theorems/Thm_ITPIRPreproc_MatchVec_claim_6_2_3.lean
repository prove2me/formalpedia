-- Prove2me | Theorems.Thm_ITPIRPreproc_MatchVec_claim_6_2_3
-- name    : ITPIRPreproc.MatchVec.claim_6_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:12:47.646398+00:00
-- url     : https://prove2.me/theorems/0ef0f2e8-a87b-4f1f-839c-7e2ea0a35408
-- title:
--   Claim 6.2.3 — the activation-bit decoder never errs and recovers $D[a^\star,b^\star]$ with probability $1/2$
-- statement:
--   Let $m=2^h$ with $h\ge3$, and let $u_a,v_a\in\mathbb Z_6^d$ satisfy (7) with the vectors $v_a\bmod2$ pairwise distinct. For every database $D\in\{0,1\}^{m\times m}$ and target $i=(a^\star,b^\star)\in[m]\times\mathbb F_2^h$, sample
--   $$(R,\rho)\leftarrow\mathcal R^+_i,\qquad (Q,u)\leftarrow\mathsf{Query}(i,(R,\rho)),$$
--   and set $z=\mathsf{Hint}(D,(R,\rho))$ and $\mathit{ans}=\mathsf{Answer}(D,Q)$. Then
--   $$\Pr\big[\mathsf{Decode}(i,(R,\rho),z,Q,u,\mathit{ans})\in\{D[a^\star,b^\star],\bot\}\big]=1,\qquad \Pr\big[\mathsf{Decode}(i,(R,\rho),z,Q,u,\mathit{ans})=D[a^\star,b^\star]\big]=\frac12.$$
--
--   This is property (iii) of Definition 4.1 for the activation-bit primitive, with recovery probability exactly one half.
--
--   **Formalization Note** The decoder's value lies in $\mathbb F_3\cup\{\bot\}$; the bit $D[a^\star,b^\star]$ is compared through its embedding $0,1\in\mathbb F_3$.
--
--   Differences from the source:
--   - encoding: Pr over (R, ρ) ← R⁺_i and the coins of Query → average over R⁺_i of the probability under the uniform coins (γ, δ); reason: uniform laws on finite sets; same probabilities
--   - encoding: Decode(…) ∈ {D[a⋆, b⋆], ⊥} with D[a⋆, b⋆] a bit and Decode a value of F₃ → Option (ZMod 3), compared with the image 0/1 ∈ F₃ of the bit D a⋆ (colIdx b⋆); reason: the paper's decoder returns an element of F₃ or ⊥; same statement
-- source:
--   Jesko Dujmovic, Zhengnan Lai, Daniel Wichs, Nearly Optimal Information-Theoretic PIR with Client Preprocessing, STOC 2027 submission #572 (October 2026), Claim 6.2.3, printed p.23 (PDF p.25)

import Mathlib
import Definitions.Def_ITPIRPreproc_MatchVec_ActivationPrimitive

open scoped ENNReal

namespace ITPIRPreproc.MatchVec

/-- Claim 6.2.3, printed p.23 (PDF p.25). For every database `D ∈ {0,1}^{m×m}` and target
`i = (a⋆, b⋆)`, with `(R, ρ) ← R⁺_i`, `(Q, u) ← Query(i, (R, ρ))`, `z = Hint(D, (R, ρ))` and
`ans = Answer(D, Q)`: the decoder's output lies in `{D[a⋆, b⋆], ⊥}` with probability `1` and equals
`D[a⋆, b⋆]` with probability exactly `1/2`. -/
theorem claim_6_2_3 (h d : ℕ) (u v : Fin (2 ^ h) → Fin d → ZMod 6) (hh : 3 ≤ h)
    (hmv : IsMVFamily (2 ^ h) d u v) :
    ∀ (D : DB h) (i : Pos h),
      avgOver (actCompat v i) (fun K => (actQuery u i K).toOuterMeasure
          {p | actDecode u i K (actHint v D K) p.1 p.2 (actAnswer v D p.1) =
                some (bitF3 (D i.1 (colIdx i.2))) ∨
              actDecode u i K (actHint v D K) p.1 p.2 (actAnswer v D p.1) = none}) = 1 ∧
      avgOver (actCompat v i) (fun K => (actQuery u i K).toOuterMeasure
          {p | actDecode u i K (actHint v D K) p.1 p.2 (actAnswer v D p.1) =
                some (bitF3 (D i.1 (colIdx i.2)))}) = 2⁻¹ := by sorry

end ITPIRPreproc.MatchVec
