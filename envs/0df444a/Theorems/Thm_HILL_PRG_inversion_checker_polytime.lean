-- Prove2me | Theorems.Thm_HILL_PRG_inversion_checker_polytime
-- name    : HILL.PRG.inversion_checker_polytime
-- status  : Proved
-- author  : @Victorized
-- created : 2026-10-24T04:55:09.133632+00:00
-- url     : https://prove2.me/theorems/2f639b4d-3ad1-4e71-a728-48fd8edd4a35
-- title:
--   Polynomial-time closure of the explicit inversion checker
-- statement:
--   Let $T,L,E,I$ be total polynomial-time functions on bit strings. They serve as unary length programs, an evaluator, and an inverter. Then the explicit inversion-checking program built from them is polynomial time:
--
--   $$
--   T,L,E,I\in\mathrm{FP}\quad\Longrightarrow\quad
--   \operatorname{Check}(T,L,E,I)\in\mathrm{FP}.
--   $$
--
--   The checker reads the unary security parameter, separates the image from the coin suffix using the length program, runs the inverter, checks the candidate seed length, and compares the evaluated image with the target. The function is defined on every bit string, including malformed encodings. This assertion supplies the computational closure step in the reverse implication of the HILL equivalence.
--
--   **Formalization Note** Polynomial time means Mathlib's bundled TM2 machine model with polynomial running-time bounds. This open theorem does not assume cryptographic hardness and does not import the reverse implication.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Håstad, Impagliazzo, Levin, Luby, A Pseudorandom Generator from Any One-Way Function, SIAM J. Comput. 28(4), 1999, p. 1387, Theorem 6.3, reverse implication attributed to Levin (1987); https://www.cs.bu.edu/fac/lnd/pdf/hill.pdf. The checking algorithm and quantitative counting bound are an explicit formalization of the standard inverter-to-distinguisher reduction.

import Definitions.Def_HILL_PRG_InversionCheck

namespace HILL.PRG

/-- Polynomial-time closure for the explicit inverter checking program. -/
theorem inversion_checker_polytime (T L E I : Bits → Bits)
    (hT : PolyTimeComputable T) (hL : PolyTimeComputable L)
    (hE : PolyTimeComputable E) (hI : PolyTimeComputable I) :
    PolyTimeComputable (inversionChecker T L E I) := by sorry

end HILL.PRG
