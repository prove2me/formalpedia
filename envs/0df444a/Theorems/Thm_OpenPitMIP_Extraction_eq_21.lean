-- Prove2me | Theorems.Thm_OpenPitMIP_Extraction_eq_21
-- name    : OpenPitMIP.Extraction.eq_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:43:21.625739+00:00
-- url     : https://prove2.me/theorems/f4e0b354-f5e8-4b2b-928b-32c627af315e
-- title:
--   (21), p. 1432 — under full integrality every cumulative variable w_{c,t} is 0 or 1
-- statement:
--   Consider an instance of the PCPSP-C satisfying the standing assumptions, and let $(x,y)$ be feasible for the PCPSP-F, i.e. with full integrality $x_{c,t}\in\{0,1\}$ (10). Then the cumulative variables $w_{c,t}=\sum_{t'=1}^{t}x_{c,t'}$ satisfy
--   $$w_{c,t}\in\{0,1\}\qquad\forall c\in\mathcal C,\ \forall t\in\mathcal T.\tag{21}$$
--
--   This is the form of the integrality condition used in the proofs of the clique, early start and diamond cuts.
--
--   **Formalization Note** The partial integrality counterpart (22) is not a separate statement: in this formalization condition (11) is already written in the cumulative variables, so (22) is (11) verbatim.
-- source:
--   Oper. Res. 68(5), §5, (21), p. 1432

import Mathlib
import Definitions.Def_OpenPitMIP_Extraction_Setting

namespace OpenPitMIP.Extraction

/-- Display (21), §5, p. 1432: at every feasible point of the PCPSP-F (full integrality (10)),
every cumulative variable `w_{c,t} = cum x c t` is `0` or `1`. -/
theorem eq_21 {B D C : Type} [Fintype B] [Fintype D] [Fintype C] {T m : ℕ}
    (I : PCPSPC B D C T m) (hI : I.Standing)
    (x : C → Fin T → ℝ) (y : B → D → Fin T → ℝ) (hxy : I.Feasible .F x y) :
    ∀ (c : C) (t : Fin T), PCPSPC.cum x c t = 0 ∨ PCPSPC.cum x c t = 1 := by sorry

end OpenPitMIP.Extraction
