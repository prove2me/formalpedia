-- Prove2me | Theorems.Thm_MoreauProx_Characterization_prox_nonexpansive
-- name    : MoreauProx.Characterization.prox_nonexpansive
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:19:37.235466+00:00
-- url     : https://prove2.me/theorems/ff7cd9c6-77dd-43f4-81a5-a2cc4eabb993
-- title:
--   Proposition 5.b — prox_f is nonexpansive, hence continuous
-- statement:
--   Let $H$ be a real Hilbert space and $f \in \Gamma_0(H)$. For all $z, z' \in H$,
--   $$
--   \|\operatorname{prox}_f z - \operatorname{prox}_f z'\| \le \|z - z'\|,
--   $$
--   so the map $\operatorname{prox}_f$ is continuous from $H$ (norm topology) to $H$ (norm topology).
--
--   Nonexpansiveness of proximal maps is the basis of their use in numerical methods, and it is one of the two properties (with the subgradient selection) that characterize prox maps in Corollary 10.c.
--
--   **Formalization Note** $\operatorname{prox}_f$ is the choice-based function of the definitions file; under $f \in \Gamma_0(H)$ it returns the unique minimizer of $u \mapsto \tfrac12\|u - z\|^2 + f(u)$. Both clauses of the paper's statement, the inequality and the continuity, are stated.
-- source:
--   Moreau, Proximité et dualité dans un espace hilbertien, Bull. Soc. Math. France 93 (1965), p. 282, Proposition 5.b, (5.2)

import Mathlib
import Definitions.Def_MoreauProx_Characterization_Prox
open scoped InnerProductSpace

namespace MoreauProx.Characterization

theorem prox_nonexpansive {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → EReal) (hf : GammaZero f) :
    (∀ z z' : H, ‖prox f z - prox f z'‖ ≤ ‖z - z'‖) ∧ Continuous (prox f) := by sorry

end MoreauProx.Characterization
