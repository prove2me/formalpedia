-- Prove2me | Theorems.Thm_MIPRE_Cost_Data_encode_of_decode_bitStr
-- name    : MIPRE.Cost.Data.encode_of_decode_bitStr
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:30:39.677415+00:00
-- url     : https://prove2.me/theorems/459c533f-f570-4037-b700-94c868a0b906
-- title:
--   Decoding a bit string from data succeeds only on its encoding
-- statement:
--   The ambient model computes on binary trees: `Data` has the two constructors `nil` and `cons a b`. A bit is encoded as $\mathrm{false} \mapsto \mathrm{nil}$, $\mathrm{true} \mapsto \mathrm{cons}(\mathrm{nil}, \mathrm{nil})$, and a bit string $l \in \{0,1\}^*$ (`BitStr = List Bool`) as the `cons`-chain of its bits ending in `nil`, so $\mathrm{encode}(l) = \mathrm{cons}(\mathrm{encode}\,l_0, \mathrm{cons}(\mathrm{encode}\,l_1, \ldots \mathrm{nil}))$. Decoding, `decode : Data → Option BitStr`, reads the chain back elementwise: `nil` decodes to the empty string, `cons a d` to $b :: l$ when $a$ decodes to the bit $b$ and $d$ to $l$, and to `none` whenever a cell is neither `nil` nor `cons nil nil`. The class `SizedEncoding` guarantees $\mathrm{decode}(\mathrm{encode}\,l) = \mathrm{some}\,l$; this theorem is the converse: for every datum $d$ and bit string $l$,
--
--   $$ \mathrm{decode}(d) = \mathrm{some}(l) \ \Longrightarrow\ \mathrm{encode}(l) = d. $$
--
--   So decoding is injective where it succeeds, and the data on which it succeeds are exactly the encodings of bit strings. The descriptions of the halting reduction travel as bit strings and their parameters as binary numerals read back from data; `encode_natOf` uses this to show that a normalized parameter is the encoding of the number it denotes.
--
--   **Formalization Note** The statement is `MIPRE.Cost.Data.encode_of_decode_bitStr`, with `d : Data` and `l : BitStr` implicit and `h : (decode d : Option BitStr) = some l`; `decode` and `encode` are those of the `SizedEncoding BitStr` instance, `Data.toList? Data.toBool?` and `Data.ofList Data.ofBool`. The type ascription `(decode d : Option BitStr)` selects the bit-string instance, as `Data` also decodes to naturals and pairs. No size or well-formedness hypothesis is needed.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Descriptions.lean#L141-L170; internal lemma of the formalization of blueprint rem:compression-abstract, item 1 (descriptions as bit strings), used in thm:halting, https://vidick.github.io/MIPRE-formalization/blueprint/

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

theorem MIPRE.Cost.Data.encode_of_decode_bitStr {d : Data} {l : BitStr}
    (h : (decode d : Option BitStr) = some l) : (encode l : Data) = d := by sorry
