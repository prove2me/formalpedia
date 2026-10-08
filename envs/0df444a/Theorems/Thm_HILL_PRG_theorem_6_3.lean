-- Prove2me | Theorems.Thm_HILL_PRG_theorem_6_3
-- name    : HILL.PRG.theorem_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:11:19.712879+00:00
-- url     : https://prove2.me/theorems/6b5367e0-e7e1-4977-8b6a-f8f7eaaf0203
-- title:
--   Theorem 6.3 — one-way functions exist iff PRGs exist
-- statement:
--   The paper's main equivalence says that polynomial-time one-way functions exist exactly when polynomial-time pseudorandom generators exist:
--
--   $$
--   (\exists F\;\mathrm{OWF}(F))\quad\Longleftrightarrow\quad
--   (\exists G\;\mathrm{PRG}(G)).
--   $$
--
--   One-wayness means every uniform polynomial-time probabilistic inverter succeeds with negligible probability. Pseudorandomness means a strictly stretching generator whose output is indistinguishable from a uniform string by every uniform polynomial-time probabilistic distinguisher. The quantifiers range over function ensembles, so the input and output lengths may vary polynomially with the security parameter.
--
--   **Formalization Note** The source's quantitative time–success ratios and reduction-preservation classes are replaced by the qualitative negligible-success notion used for Theorem 6.3. The underlying machine is Mathlib's TM2 model via the published `Levin2003_owf_model`; its separate length-preserving `OneWay` predicate is not used.
-- source:
--   Håstad, Impagliazzo, Levin and Luby, A pseudorandom generator from any one-way function, SIAM J. Comput. 28(4), 1999, p. 1387, Theorem 6.3

import Mathlib
import Definitions.Def_HILL_PRG_Model

namespace HILL.PRG

/-- Theorem 6.3, p. 1387: one-way functions exist iff PRGs exist. -/
theorem theorem_6_3 :
    (∃ F : FunEns, IsOWF F) ↔
      (∃ G : FunEns, IsPRG G (fun _ => 0)) := by sorry

end HILL.PRG
