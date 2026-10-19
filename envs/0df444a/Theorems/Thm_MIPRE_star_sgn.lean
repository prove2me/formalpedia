-- Prove2me | Theorems.Thm_MIPRE_star_sgn
-- name    : MIPRE.star_sgn
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:13:28.28896+00:00
-- url     : https://prove2.me/theorems/bc3c5321-974b-4529-8886-e750b3429b8d
-- title:
--   Lemma star_sgn of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Foundations.Sign` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The sign of a bit. `sgn x = (-1)^x` for `x : ZMod 2`, as a complex number. It is the character group of `𝔽₂` written multiplicatively, and it is what every `±1`-observable in this development is built from: the observable of a two-outcome measurement, the phase of a Weyl operator in characteristic two, and the sign a Magic Square constraint carries. Characteristic two is why this is a *sign* and not a root of unity. Over `𝔽_p` the generalized Pauli operators carry phases `e^{2πi/p}`; this project's fields are always of admissible size `q = 2^k`, so `p = 2` and every phase is real. That…
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--
--   theorem MIPRE.star_sgn (x : ZMod 2) : star (sgn x) = sgn x
--   ```
--
--   **Formalization Note** `MIPRE.star_sgn` is declared in `MIPRE/Foundations/Sign.lean`, lines 39–40. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Sign.lean#L39-L40; blueprint def:generalized-pauli

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Sign

open MIPRE

theorem MIPRE.star_sgn (x : ZMod 2) : star (sgn x) = sgn x := by sorry
