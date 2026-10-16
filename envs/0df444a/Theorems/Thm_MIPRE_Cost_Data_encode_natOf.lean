-- Prove2me | Theorems.Thm_MIPRE_Cost_Data_encode_natOf
-- name    : MIPRE.Cost.Data.encode_natOf
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:31:47.082985+00:00
-- url     : https://prove2.me/theorems/d07374fe-ae57-41b9-9510-ea9dc7efea6d
-- title:
--   The normalized parameter of a datum is the binary encoding of the number it denotes
-- statement:
--   Data are binary trees (`nil`, `cons`); a natural number $n$ is encoded as the list of its binary digits `Nat.bits n` (least significant first, with no trailing zero), each bit as $\mathrm{false} \mapsto \mathrm{nil}$, $\mathrm{true} \mapsto \mathrm{cons}(\mathrm{nil},\mathrm{nil})$ and the list as a `cons`-chain ending in `nil`; a datum decodes to a natural (`decode : Data → Option ℕ`) by decoding it as a bit string and folding `Nat.bit` over the result. A datum $d$ is a canonical binary numeral (`isCanonBin d`) when it decodes to a bit string that is empty or ends in $\mathrm{true}$. The total normalization is $\mathrm{normBin}(d) = d$ if $d$ is canonical and $\mathrm{nil}$ (the encoding of $0$) otherwise, and the number a datum denotes is $\mathrm{natOf}(d)$, the decoding of $\mathrm{normBin}(d)$ as a natural, with default $0$. For every datum $d$,
--
--   $$ \mathrm{encode}\bigl(\mathrm{natOf}(d)\bigr) \;=\; \mathrm{normBin}(d). $$
--
--   Every string of the compressibility criterion names a parameter through `natOf` applied to the left component of the datum it parses to (`descLam`), with no validity condition on strings; this theorem says the normalized datum is the encoding of that parameter, which is what bounds the parameter by the datum's size (`natOf_lt`, hence `descLam_lt`), the fact the answer budget of the halting reduction depends on.
--
--   **Formalization Note** The statement is `MIPRE.Cost.Data.encode_natOf`, with `d : Data` explicit and the ascription `(encode (natOf d) : Data)` selecting the `SizedEncoding ℕ` instance. `normBin d` unfolds to `if isCanonBin d then d else nil` and `natOf d` to `((decode (normBin d) : Option ℕ)).getD 0`; both are total, every non-canonical datum reading as `0` with `normBin d = nil = encode 0`. `isCanonBin` is a `Bool` computed from `(decode d : Option BitStr)`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Descriptions.lean#L237-L253; internal lemma of the formalization of blueprint rem:compression-abstract, item 1 (descriptions as bit strings), used in thm:halting, https://vidick.github.io/MIPRE-formalization/blueprint/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Data

theorem MIPRE.Cost.Data.encode_natOf (d : Data) : (encode (natOf d) : Data) = normBin d := by sorry
