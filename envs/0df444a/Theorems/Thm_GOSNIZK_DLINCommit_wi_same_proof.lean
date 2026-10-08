-- Prove2me | Theorems.Thm_GOSNIZK_DLINCommit_wi_same_proof
-- name    : GOSNIZK.DLINCommit.wi_same_proof
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:04.113869+00:00
-- url     : https://prove2.me/theorems/51092703-887f-48b8-b5cd-2e55ac2e1f4e
-- title:
--   Proof of Theorem 4 (p. 13) — openings (0, r₀, s₀) with t and (1, r₁, s₁) with t + r₀s₁ − s₀r₁ give the same proof
-- statement:
--   Let $(p, \mathbb G, \mathbb G_T, e, g)$ be a DLIN bilinear group and $ck$ a perfectly hiding commitment key of Figure 2 with trapdoor $(r_u, s_v)$. For $r_0, s_0 \in \mathbb Z_p$ put $(r_1, s_1) = (r_0 - r_u, s_0 - s_v)$, so that $(0, r_0, s_0)$ and $(1, r_1, s_1)$ open the same commitment. Then for every $t \in \mathbb Z_p$,
--   $$P_{01}\bigl(ck, 0, (r_0, s_0); t\bigr) = P_{01}\bigl(ck, 1, (r_1, s_1); t + r_0 s_1 - s_0 r_1\bigr).$$
--
--   Since $t \mapsto t + r_0 s_1 - s_0 r_1$ is a bijection of $\mathbb Z_p$, this gives perfect witness indistinguishability and, with the explicit randomness $t'$, perfect non-erasure witness indistinguishability.
--
--   **Formalization Note** $P_{01}$ is the prover of Figure 2 with the signs of $t$ in $\pi_{12}$ and $\pi_{21}$ swapped (see the definition). For the prover as printed the identity is false.
-- source:
--   Groth, Ostrovsky, Sahai, New Techniques for Noninteractive Zero-Knowledge, J. ACM 59(3) (2012), authors' version of March 7, 2011, p. 13, proof of Theorem 4 ('All we need to observe now is ...')

import Mathlib
import Definitions.Def_GOSNIZK_DLINCommit_Properties

namespace GOSNIZK.DLINCommit

variable {G GT : Type*} [CommGroup G] [Fintype G] [CommGroup GT] [Fintype GT]

/-- Proof of Theorem 4, p. 13: on a perfectly hiding key with trapdoor `(r_u, s_v)`, put
`(r₁, s₁) = (r₀ − r_u, s₀ − s_v)`. Then opening `(0, r₀, s₀)` with proof randomness `t` gives the same
proof as opening `(1, r₁, s₁)` with randomness `t′ = t + r₀s₁ − s₀r₁` (for the corrected `P01`). -/
theorem wi_same_proof (S : DLINSetup G GT) (ck : CommitKey G) (ru sv : ZMod S.p)
    (hck : S.IsHidingKey ck (ru, sv)) (r₀ s₀ t : ZMod S.p) :
    S.P01 ck 0 (r₀, s₀) t =
      S.P01 ck 1 (r₀ - ru, s₀ - sv) (t + r₀ * (s₀ - sv) - s₀ * (r₀ - ru)) := by sorry

end GOSNIZK.DLINCommit
