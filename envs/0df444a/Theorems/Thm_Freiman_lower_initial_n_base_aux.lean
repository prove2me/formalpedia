-- Prove2me | Theorems.Thm_Freiman_lower_initial_n_base_aux
-- name    : Freiman.lower_initial_n_base_aux
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:20:16.119372+00:00
-- url     : https://prove2.me/theorems/b205da0c-c40d-4626-a72b-109f252dfc3a
-- title:
--   Freiman lower construction: initial n base aux
-- statement:
--   Direct exact n=0 source-word evaluation; it is separate from the normalized n>0 matrix.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-contacts; exact initial contact appendix

import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

open scoped BigOperators

theorem Freiman.lower_initial_n_base_aux : certFieldVal (lowerInitialNBase .aux) =
    (let w := lowerInitialNWords .aux
     prefixEval ((w 0).1++(w 0).2) lowerTau + prefixEval ((w 1).1++(w 1).2) lowerTau -
     prefixEval ((w 2).1++(w 2).2) lowerTau - prefixEval ((w 3).1++(w 3).2) lowerTau) := by
  sorry
