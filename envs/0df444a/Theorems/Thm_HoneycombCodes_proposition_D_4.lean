-- Prove2me | Theorems.Thm_HoneycombCodes_proposition_D_4
-- name    : HoneycombCodes.proposition_D_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:29:20.292206+00:00
-- url     : https://prove2.me/theorems/4f77f099-2f04-4b22-977f-690880bca08d
-- title:
--   Proposition D.4 — structure of an interior 2MQC minimizer
-- statement:
--   Let $(u,v)$ minimize (127), and put $A=A_\delta(u,v)$. If $A<1$, then
--
--   $$
--   0<v<u<1,\qquad \mathcal E(u,v,A)=\delta,\qquad A>u^2,\qquad A>2\delta.
--   $$
--
--   These inequalities place the bridge of Lemma D.5 inside the constant-weight parameter range.
--
--   Differences from the source:
--
--   - encoding: '(u, v) minimize (127)' → IsR2MQCMinimizer δ u v: (u, v) ∈ F_δ and Ψ_δ(u, v) ≤ Ψ_δ at every point of F_δ; reason: the definition of a minimizer of (127)
--   - reading: the standing range of δ in Appendix D → hypotheses 0 < δ < 1/2; reason: App. D works throughout at 0 < δ < 1/2
-- source:
--   W. Gay, F. Granha Jeronimo, L. Liu, The Honeycomb Framework for Code Bounds, arXiv:2608.20287v2 (sha256 f4b07e318538a352116042dc4da0d4e9d47cfd979cf302c7fce3324584a3cd51), App. D.3, Proposition D.4, p.62 (PDF 64)

import Mathlib
import Definitions.Def_HoneycombCodes_R2MQC

set_option autoImplicit false

namespace HoneycombCodes

/-- **Proposition D.4**, Gay, Granha Jeronimo, Liu, *The Honeycomb Framework for Code Bounds*, arXiv:2608.20287v2 (sha256 f4b07e31…cd51), App. D.3, p.62 (PDF 64). Let `(u, v)` minimize (127) and put
`A = A_δ(u, v)`. If `A < 1`, then `0 < v < u < 1`, `E(u, v, A) = δ`, `A > u²`, `A > 2δ`.

**Formalization Note.** Stated for `0 < δ < 1/2`; "(u, v) minimize (127)" is
`IsR2MQCMinimizer`: a point of `F_δ` attaining the minimum of `Ψ_δ` over `F_δ`. -/
theorem proposition_D_4 (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2) (u v : ℝ)
    (hmin : IsR2MQCMinimizer δ u v) (hA : Adelta δ u v < 1) :
    0 < v ∧ v < u ∧ u < 1 ∧ Efun u v (Adelta δ u v) = δ ∧ u ^ 2 < Adelta δ u v ∧
      2 * δ < Adelta δ u v := by sorry

end HoneycombCodes
