-- Prove2me | Theorems.Thm_MatMulPolyBarrier_Operational_renumbering_legs
-- name    : MatMulPolyBarrier.Operational.renumbering_legs
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:08:24.153898+00:00
-- url     : https://prove2.me/theorems/37c372ff-c3d5-4810-a5b2-6855be2b3ad3
-- title:
--   §5.7 — renumbering the legs of an expression changes $F^\star_\theta$ into $F^\star_{\theta'}$, $\theta'$ renumbered the same way
-- statement:
--   Let $\theta\in\Theta$, let $\pi$ be a permutation of $\{1,2,3\}$ and let $E\in\mathcal F$. Write $\pi\cdot E$ for $E$ with its legs renumbered by $\pi$ (leg $s$ becomes leg $\pi(s)$). Then
--   $$F^\star_\theta(\pi\cdot E)=F^\star_{\theta'}(E),\qquad \theta'_s:=\theta_{\pi(s)},$$
--   i.e. renumbering the legs changes $F^\star_\theta$ into $F^\star_{\theta'}$, where $\theta'$ is $\theta$ with its entries renumbered in the same way. This reduces Proposition 5.9 to the properties of Definition 5.3 without the permutations.
--
--   Differences from the source:
--   - reading: "θ′ is θ with its entries renumbered in the same way" → θ′ s = θ (π s), the entry of θ that faces the old leg s after the move; reason: of the two directions (θ ∘ π or θ ∘ π⁻¹) this is the one under which the sentence is true for every π (the other fails for 3-cycles, checked numerically), and it is the paper's "values do not change when the legs and the entries of θ are renumbered together" (p. 40)
--   - encoding: "an expression" → E : FExpr with E.WF (E ∈ F); legs and θ indexed by Fin 3; reason: the claim is about elements of F
-- source:
--   Amanov, van den Berg, Zuiddam, Multiplying matrices via polynomials: operational asymptotic spectrum barrier, STOC 2027 submission (manuscript sha256 38bd5183…), p. 42, §5.7, proof of Proposition 5.9 (leg renumbering)

import Mathlib
import Definitions.Def_MatMulPolyBarrier_Operational_FExpr
import Definitions.Def_MatMulPolyBarrier_Operational_Fstar

set_option autoImplicit false

namespace MatMulPolyBarrier.Operational

/-- §5.7, proof of Proposition 5.9, p. 42: renumbering the legs of an expression `E ∈ F` by `π`
(leg `s` becomes leg `π(s)`) changes `F⋆_θ` into `F⋆_{θ'}`, where `θ'` is `θ` with its entries
renumbered in the same way: `θ'_s = θ_{π(s)}`, the entry of `θ` that now faces the old leg `s`. -/
theorem renumbering_legs (θ : Fin 3 → ℝ) (hθ : InTheta θ) (π : Equiv.Perm (Fin 3)) (E : FExpr)
    (hE : E.WF) :
    Fstar θ (E.perm π) = Fstar (fun s => θ (π s)) E := by sorry

end MatMulPolyBarrier.Operational
