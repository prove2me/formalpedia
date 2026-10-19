-- Prove2me | Theorems.Thm_MIPRE_sgn_add
-- name    : MIPRE.sgn_add
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:13:23.995886+00:00
-- url     : https://prove2.me/theorems/b6445593-fcd3-4970-827b-5170e98b08af
-- title:
--   Lemma sgn_add of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Foundations.Sign` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The sign of a bit. `sgn x = (-1)^x` for `x : ZMod 2`, as a complex number. It is the character group of `𝔽₂` written multiplicatively, and it is what every `±1`-observable in this development is built from: the observable of a two-outcome measurement, the phase of a Weyl operator in characteristic two, and the sign a Magic Square constraint carries. Characteristic two is why this is a *sign* and not a root of unity. Over `𝔽_p` the generalized Pauli operators carry phases `e^{2πi/p}`; this project's fields are always of admissible size `q = 2^k`, so `p = 2` and every phase is real. That…
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--
--   theorem MIPRE.sgn_add (x y : ZMod 2) : sgn (x + y) = sgn x * sgn y
--   ```
--
--   **Formalization Note** `MIPRE.sgn_add` is declared in `MIPRE/Foundations/Sign.lean`, lines 30–34. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Sign.lean#L30-L34; blueprint def:generalized-pauli

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Sign

open MIPRE

theorem MIPRE.sgn_add (x y : ZMod 2) : sgn (x + y) = sgn x * sgn y := by sorry
