-- Prove2me | Theorems.Thm_OpenPitMIP_UltPit_exists_optimal
-- name    : OpenPitMIP.UltPit.exists_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:42:49.417885+00:00
-- url     : https://prove2.me/theorems/ed8d81c8-feab-4c18-b378-2cb38fd921f3
-- title:
--   §2.1, p. 1427 — under (10) or (11) the PCPSP-C has an optimal solution whenever it is feasible
-- statement:
--   Consider an instance of the PCPSP-C (formulation (1)–(7)) under the standing assumptions of §2.1, with either the full integrality condition (10) or the partial integrality condition (11). If the PCPSP-C has a feasible solution, then it has an optimal solution: a feasible $(x^*, y^*)$ with
--   $$\sum_{b}\sum_{d}\sum_{t} p_{b,d,t}\, y_{b,d,t} \le \sum_{b}\sum_{d}\sum_{t} p_{b,d,t}\, y^*_{b,d,t}$$
--   for every feasible $(x, y)$.
--
--   The paper derives this from the boundedness of the feasible set; it guarantees that the minimal optimal solutions of Theorem 1 are about a nonempty set of optima.
--
--   **Formalization Note** Boundedness of the feasible set relies on every cluster being nonempty (standing assumption), which forces $x \ge 0$.
-- source:
--   Oper. Res. 68(5), §2.1, p. 1427

import Mathlib
import Definitions.Def_OpenPitMIP_UltPit_Setting

namespace OpenPitMIP.UltPit

open PCPSPC

/-- §2.1, p. 1427: under either integrality condition (10) or (11) the PCPSP-C has a bounded
feasible set, so an optimal solution exists whenever the feasible set is nonempty. -/
theorem exists_optimal {B D C : Type} [Fintype B] [Fintype D] [Fintype C] {T m : ℕ}
    (I : PCPSPC B D C T m) (hI : I.Standing) (κ : Integrality)
    (hfeas : ∃ x y, I.Feasible κ x y) :
    ∃ x y, I.Optimal κ x y := by sorry

end OpenPitMIP.UltPit
