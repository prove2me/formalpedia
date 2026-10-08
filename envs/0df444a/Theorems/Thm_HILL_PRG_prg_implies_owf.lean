-- Prove2me | Theorems.Thm_HILL_PRG_prg_implies_owf
-- name    : HILL.PRG.prg_implies_owf
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:11:09.451144+00:00
-- url     : https://prove2.me/theorems/776fdcf6-3f5d-48ca-9908-98c94fdc226d
-- title:
--   Proof of Theorem 6.3 — PRG existence implies OWF existence
-- statement:
--   If a polynomial-time pseudorandom generator exists, then a polynomial-time one-way function exists:
--
--   $$
--   (\exists G\;\mathrm{PRG}(G))\Longrightarrow(\exists F\;\mathrm{OWF}(F)).
--   $$
--
--   This is the direction cited to Levin in the proof of Theorem 6.3. It is an existential claim: the source generator itself need not be one-way if it stretches by only one bit.
--
--   **Formalization Note** Both primitives use uniform adversaries and qualitative negligible success. The paper attributes this direction to [Levin87] without a separate numbered result; the quantitative reduction is outside scope.
-- source:
--   Håstad, Impagliazzo, Levin and Luby, A pseudorandom generator from any one-way function, SIAM J. Comput. 28(4), 1999, p. 1387, proof of Theorem 6.3 (first direction)

import Mathlib
import Definitions.Def_HILL_PRG_Model

namespace HILL.PRG

/-- The Levin87 direction cited in the proof of Theorem 6.3, p. 1387. -/
theorem prg_implies_owf :
    (∃ G : FunEns, IsPRG G (fun _ => 0)) →
      ∃ F : FunEns, IsOWF F := by sorry

end HILL.PRG
