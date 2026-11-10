-- Prove2me | Theorems.Thm_HoneycombCodes_theorem_6_3
-- name    : HoneycombCodes.theorem_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:30:52.851264+00:00
-- url     : https://prove2.me/theorems/d1590a54-9f79-4516-8d89-ae6c5d5c1362
-- title:
--   Theorem 6.3 — the one-sided face strictly improves the whole cube
-- statement:
--   For every $0<\delta<1/2$,
--
--   $$
--   \kappa_{HC}(\delta)\le\kappa_{face}(\delta)<\kappa_H(\delta).
--   $$
--
--   Opening a single second row ($\eta=0$, $\rho>0$) already gives a bound strictly below the whole-cube exponent of OpenAI.
--
--   Differences from the source: none.
-- source:
--   W. Gay, F. Granha Jeronimo, L. Liu, The Honeycomb Framework for Code Bounds, arXiv:2608.20287v2 (sha256 f4b07e318538a352116042dc4da0d4e9d47cfd979cf302c7fce3324584a3cd51), §6.2, Theorem 6.3, p.30 (PDF 32)

import Mathlib
import Definitions.Def_HoneycombCodes_kappaHC
import Definitions.Def_HoneycombCodes_kappaFace

set_option autoImplicit false

namespace HoneycombCodes

/-- **Theorem 6.3**, Gay, Granha Jeronimo, Liu, *The Honeycomb Framework for Code Bounds*, arXiv:2608.20287v2 (sha256 f4b07e31…cd51), p.30 (PDF 32). For every `0 < δ < 1/2`,
`κ_HC(δ) ≤ κ_face(δ) < κ_H(δ)`. -/
theorem theorem_6_3 (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    kappaHC δ ≤ kappaFace δ ∧ kappaFace δ < kappaH δ := by sorry

end HoneycombCodes
