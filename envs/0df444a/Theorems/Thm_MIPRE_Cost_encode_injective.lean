-- Prove2me | Theorems.Thm_MIPRE_Cost_encode_injective
-- name    : MIPRE.Cost.encode_injective
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-16T15:22:27.044562+00:00
-- url     : https://prove2.me/theorems/d7a83abd-7acb-4010-8d55-171ec7850324
-- title:
--   Lemma encode_injective of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Foundations.Cost.Encoding` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Size-aware encodings. Interface between ordinary types and the ambient model: a `SizedEncoding α` renders `a : α` as a value `encode a : Data`, and `esize a` is its size (the length of its preorder serialization `Data.toBits`), an honest bit-length up to a constant factor. All polynomial-time statements (`Cost.PolyTime`) are relative to these encodings. Conventions: * bits are `false ↦ nil` and `true ↦ cons nil nil`; * lists are `cons`-chains ending in `nil`, so a bit string of length `n` has size between `2n + 1` and `4n + 1`; * natural numbers are encoded in **binary** (LSB first,…
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Cost
--
--   theorem MIPRE.Cost.encode_injective {α : Type*} [SizedEncoding α] : Function.Injective (encode : α → Data)
--   ```
--
--   **Formalization Note** `MIPRE.Cost.encode_injective` is declared in `MIPRE/Foundations/Cost/Encoding.lean`, lines 51–55. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Encoding.lean#L51-L55

import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B

open MIPRE
open MIPRE.Cost

theorem MIPRE.Cost.encode_injective {α : Type*} [SizedEncoding α] : Function.Injective (encode : α → Data) := by sorry
