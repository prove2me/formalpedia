-- Prove2me | Theorems.Thm_NOFSeparation750_CodedGIP_theorem_4_1
-- name    : NOFSeparation750.CodedGIP.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T02:43:10.089728+00:00
-- url     : https://prove2.me/theorems/038dd97b-e7a8-497b-b47f-c95b6783ec81
-- title:
--   Theorem 4.1 — constant-cost one-sided randomized protocol
-- statement:
--   Let $k\ge2$, let $V,W\le\mathbb F_q^r$ be a compatible pair with relative distance at least $3/4$, and fix ordered bases and a binary field representation using $b$ bits. For any number $\ell$ of factor words per forehead, coded GIP on native Boolean strings has a legal public-coin NOF protocol with
--   $$\operatorname{cost}(P)\le(\ell+1)b+1,\qquad \Pr[P(x)=1]=1\ (F(x)=1),\qquad \Pr[P(x)=1]\le\frac14\ (F(x)=0).$$
--   The final output bit is included in the paid communication, while public randomness is free. Specializing to Section 3's $\ell$ and $q$ gives $O_k(1)$ cost. This retains the source's rejection probability of at least $3/4$, not merely the goal's $2/3$.
--
--   Differences from the source:
--   - generalization: the selected Section 3 code pair with ℓ=2^(k+2)k and q fixed by k → every compatible pair with distance fraction 3/4 over a binary-representable field, and every ℓ≥0; reason: the protocol uses only product containment and distance; setting the field, pair, and ℓ to Section 3 gives every source instance
--   - encoding: cost O_k(1) and rejection probability at least 3/4 → a cost bound of (ℓ+1)b+1 and acceptance probability at most 1/4 on zero inputs; reason: the proof states this exact paid cost; probabilities are complements under a normalized law
--   - encoding: indices [r] and Boolean values {0,1} → zero-based Fin indices and Bool; reason: order-preserving relabeling changes no inputs, cylinders, or communication costs
-- source:
--   Haoyu Wang, Yimeng Wang, Pei Wu, STOC 2027 submission #750 (October 2026), Theorem 4.1 and its proof, p.8; §3 standing construction, p.7; canonical PDF SHA-256 b28ac89d573094bcafec49dc3a1eeadc9e95b5c3074c478d242f60a2818a42ce

import Mathlib
import Definitions.Def_NOFSeparation750_CodedGIP_Model

namespace NOFSeparation750.CodedGIP

/-- Theorem 4.1, p.8. The proof works for any compatible pair, any number of copies,
and any binary-representable field, with the same exact paid bit bound. -/
theorem theorem_4_1 (k ℓ r b : ℕ) (hk : 2 ≤ k) (ε : ℝ)
    (F : Type) [Field F] [Fintype F] (D : CodePair F r)
    (codec : (Fin b → Bool) ≃ F)
    (hD : Compatible D.small.code D.large.code k ε (3 / 4)) :
    ∃ P : PublicProtocol (fun _ : Fin k => Bits (nativeLength D ℓ b)),
      P.Bounded ((ℓ + 1) * b + 1) ∧
      P.OneSided (nativeFunction D codec ℓ k) (1 / 4) := by sorry

end NOFSeparation750.CodedGIP
