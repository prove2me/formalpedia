-- Prove2me | Theorems.Thm_K215_halts_iff_zfc_inconsistent
-- name    : K215.halts_iff_zfc_inconsistent
-- status  : Open
-- author  : @LG
-- created : 2026-11-23T22:33:08.882839+00:00
-- url     : https://prove2.me/theorems/89239598-1c42-4a42-8a7f-84ca6a050328
-- title:
--   K215 halts iff ZFC is inconsistent
-- statement:
--   This is the headline result of the `elliotglazer/k215-pa` artifact (Theorem 1, `pa-mm0/targets/final.mm0`). Let $K215$ be the fixed binary Turing machine with 215 working states (labels $0,\dots,214$) and a separate halt label $215$, given by the literal 430-row transition table transcribed in `K215.action`. Started on the blank tape, $K215$ **halts** if its run reaches the halt label after finitely many steps (`K215.Halts`). Let $\mathrm{ZFC}$ be the concrete axiom set (twelve fixed axioms together with all Separation and Replacement instances) in the fixed natural-deduction calculus for the language of set theory; $\mathrm{ZFC}$ is **inconsistent** if it derives falsity (`K215.zfcInconsistent`). The theorem asserts the equivalence
--
--   $$K215\ \text{halts}\quad\Longleftrightarrow\quad \mathrm{ZFC}\ \text{is inconsistent}.$$
--
--   It is proved with no hypotheses in Peano arithmetic in the source artifact (checked by Metamath Zero). This mission asks for a Lean 4 proof of the same equivalence against the literal machine and the concrete ZFC provability predicate.
--
--   **Formalization Note.** The machine configuration is a triple $(q,l,r)$ of natural numbers: the current cell is bit $0$ of $r$, and bit $0$ of $l$ is the cell to the left; direction $0$ moves left and $1$ moves right, exactly as in `k215TMMove`. Set-theory formulas use de Bruijn indices, and provability is derivability from a finite list of ZFC axioms in the source natural-deduction calculus.
-- source:
--   https://github.com/elliotglazer/k215-pa (pa-mm0/targets/final.mm0, Theorem 1; proved in pa-mm0/k215_final_thm1.mm0)

import Definitions.Def_k215_tm
import Definitions.Def_zfc_nd

namespace K215
theorem halts_iff_zfc_inconsistent : Halts ↔ zfcInconsistent := by sorry
end K215
