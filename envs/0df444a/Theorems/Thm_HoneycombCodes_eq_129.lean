-- Prove2me | Theorems.Thm_HoneycombCodes_eq_129
-- name    : HoneycombCodes.eq_129
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:29:15.605568+00:00
-- url     : https://prove2.me/theorems/09473984-051e-47c5-91be-9e7b54b93ede
-- title:
--   Equation (129) — $M_2(\delta)<R_{EB}(\delta)=1-g(2\delta)$
-- statement:
--   For every $0<\delta<1/2$,
--
--   $$
--   M_2(\delta)<R_{EB}(\delta):=1-g(2\delta),
--   $$
--
--   and indeed $F_\delta(0)=R_{EB}(\delta)$.
--
--   Together with (128) this rules out the degenerate lines $v=0$ and $v=u$ for a 2MQC minimizer with $A<1$.
--
--   Differences from the source:
--
--   - reading: the standing range of δ in Appendix D → hypotheses 0 < δ < 1/2; reason: App. D works throughout at 0 < δ < 1/2
-- source:
--   W. Gay, F. Granha Jeronimo, L. Liu, The Honeycomb Framework for Code Bounds, arXiv:2608.20287v2 (sha256 f4b07e318538a352116042dc4da0d4e9d47cfd979cf302c7fce3324584a3cd51), App. D.2, eq. (129), p.61 (PDF 63)

import Mathlib
import Definitions.Def_HoneycombCodes_R2MQC
import Definitions.Def_HoneycombCodes_M2

set_option autoImplicit false

namespace HoneycombCodes

/-- **Equation (129)**, Gay, Granha Jeronimo, Liu, *The Honeycomb Framework for Code Bounds*, arXiv:2608.20287v2 (sha256 f4b07e31…cd51), App. D.2, p.61 (PDF 63): `M₂(δ) < R_EB(δ) := 1 − g(2δ)`; indeed
`F_δ(0) = R_EB(δ)`.

**Formalization Note.** Stated for `0 < δ < 1/2`, the standing range of App. D. -/
theorem eq_129 (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    M2 δ < REB δ ∧ Fdelta δ 0 = REB δ := by sorry

end HoneycombCodes
