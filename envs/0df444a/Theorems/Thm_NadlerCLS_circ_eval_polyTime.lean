-- Prove2me | Theorems.Thm_NadlerCLS_circ_eval_polyTime
-- name    : NadlerCLS.circ_eval_polyTime
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-26T23:42:14.716428+00:00
-- url     : https://prove2.me/theorems/bebcbc71-9cd7-5e08-a873-30717ed3dbc3
-- title:
--   Exact evaluation of well-behaved circuits at rational points is polynomial-time
-- statement:
--   Well-behaved circuits can be evaluated exactly at rational points in polynomial time.
--
--   There is a map $E$ on binary words, computable in polynomial time, with the following property. Let $C$ be a valid well-behaved arithmetic circuit with $\mathrm{ins}$ inputs and $\mathrm{outs}$ outputs (gates $+,-,\times,\min,\max$, rational constants and the comparison $>$; every path to an output contains at most $\log_2 S$ true multiplications, $S$ the length of the binary code of its gates), and let $x\in\mathbb Q^{\mathrm{ins}}$. Then the outputs of $C$ at $x$ are rational numbers $q_1,\dots,q_{\mathrm{outs}}$, and
--
--   $$E\bigl(\langle C\rangle\,\langle x\rangle\bigr)=\langle q_1,\dots,q_{\mathrm{outs}}\rangle ,$$
--
--   where $\langle\cdot\rangle$ denotes the binary codes of circuits and of rational vectors.
--
--   This is the basic computational fact behind every checker and decoder of the mission: answers are verified, and decoded, by evaluating the circuits exactly at rational witness points. Well-behavedness is what keeps the bit length of all output values polynomial, since a straight-line program with unrestricted multiplications can produce numbers of exponential bit length.
--
--   **Formalization Note** $E$ is polynomial-time on multitape machines in the sense of Complexitylib (`Turing.MultiTapeTM.ComputableInPolyTime` with the identity encodings `encBits`), on all binary words; the codes are the public `encCirc` and `encVector`; the real outputs `Circ.eval` of the circuit at the real point `rpt x` are the casts of the $q_j$.
-- source:
--   Xiong–Vlatakis-Gkaragkounis, On the Complexity of Finding Fixed Points for Set-Valued Contractions, arXiv:2609.14101v4, Section 2, p.7 (well-behaved circuits), and Section 3, p.9 ("The circuits evaluate their own rational outputs exactly on rational inputs"; "An output of type (N2) can be checked in polynomial time by evaluating Π and d at the rational witness points"); well-behaved arithmetic circuits as in Fearnley–Goldberg–Hollender–Savani, The Complexity of Gradient Descent: CLS = PPAD ∩ PLS, arXiv:2011.01929, Section 2 (well-behaved circuits can be evaluated in polynomial time).

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Encoding
import Definitions.Def_NadlerCLS_Circ
import Definitions.Def_NadlerCLS_l1
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_PolyTime
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_List

set_option autoImplicit false

namespace NadlerCLS

open NetworkEquilibriumCLS.LinearNash

theorem circ_eval_polyTime :
    ∃ E : List Bool → List Bool,
      Turing.MultiTapeTM.ComputableInPolyTime E Turing.MultiTapeTM.encBits
        Turing.MultiTapeTM.encBits ∧
      ∀ (C : Circ) (ins outs : ℕ), C.Valid ins outs → ∀ x : Fin ins → ℚ,
        ∃ q : Fin outs → ℚ, E (encCirc C ++ encVector x) = encVector q ∧
          ∀ j, (q j : ℝ) = C.eval (rpt x) j := by sorry

end NadlerCLS
