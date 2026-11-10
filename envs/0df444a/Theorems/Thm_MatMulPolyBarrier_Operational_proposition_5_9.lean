-- Prove2me | Theorems.Thm_MatMulPolyBarrier_Operational_proposition_5_9
-- name    : MatMulPolyBarrier.Operational.proposition_5_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:08:40.630936+00:00
-- url     : https://prove2.me/theorems/36a7200c-ddc6-44ae-b5d4-3e086511b023
-- title:
--   Proposition 5.9 — every $F^\star_\theta$ is monotone under the operational preorder $\preceq$
-- statement:
--   **Proposition 5.9 (Combinations of the ingredients).** Let $\theta\in\Theta$. For all $S,T\in\mathcal F$,
--   $$T\preceq S\ \Longrightarrow\ F^\star_\theta(T)\le F^\star_\theta(S),$$
--   where $\preceq$ is the operational preorder of Definition 5.3. Together with Proposition 5.7 this gives the operational barrier, Theorem 5.4.
--
--   Differences from the source:
--   - encoding: "for all S, T ∈ F, if T ⪯ S" → for all S T : FExpr with OpLe T S; reason: OpLe relates only elements of F (reflexivity is on F, every generator requires both sides in F, renumbering and ⊕, ⊗ preserve membership), so the hypotheses S, T ∈ F are implied and would be redundant
-- source:
--   Amanov, van den Berg, Zuiddam, Multiplying matrices via polynomials: operational asymptotic spectrum barrier, STOC 2027 submission (manuscript sha256 38bd5183…), p. 42, Proposition 5.9

import Mathlib
import Definitions.Def_MatMulPolyBarrier_Operational_FExpr
import Definitions.Def_MatMulPolyBarrier_Operational_OpPreorder
import Definitions.Def_MatMulPolyBarrier_Operational_Fstar

set_option autoImplicit false

namespace MatMulPolyBarrier.Operational

/-- Proposition 5.9 (Combinations of the ingredients), p. 42: let `θ ∈ Θ`. For all `S, T ∈ F`, if
`T ⪯ S`, then `F⋆_θ(T) ≤ F⋆_θ(S)`. (`T ⪯ S` already forces `S, T ∈ F`.) -/
theorem proposition_5_9 (θ : Fin 3 → ℝ) (hθ : InTheta θ) (S T : FExpr) (h : OpLe T S) :
    Fstar θ T ≤ Fstar θ S := by sorry

end MatMulPolyBarrier.Operational
