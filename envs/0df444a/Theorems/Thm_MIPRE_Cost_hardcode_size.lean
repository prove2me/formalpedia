-- Prove2me | Theorems.Thm_MIPRE_Cost_hardcode_size
-- name    : MIPRE.Cost.hardcode_size
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:29:34.681455+00:00
-- url     : https://prove2.me/theorems/8e80a179-f014-4db1-a05c-36fe583c8040
-- title:
--   Efficient s-m-n, description size: $|s(p,d)| = |p| + \mathrm{size}(d) + 35$
-- statement:
--   Programs of the ambient cost model occur as data through their tree serialization $\mathrm{enc}(p)$ (`Prog.toData`): each constructor becomes a $\mathtt{cons}$ node whose head is a unary tag $\bar k$ (the list of $k$ copies of $\mathtt{nil}$, a tree of size $2k+1$) and whose tail holds the fields. The size of a program is $|p| := \mathrm{size}(\mathrm{enc}(p))$ (`esize`), where $\mathrm{size}$ counts the nodes of a binary tree, and $s(p,d) = \mathtt{let}\ \mathtt{cons}(\mathtt{const}\ d, \mathtt{var}\ 0)\ \mathtt{in}\ p$ (`hardcode p d`) is the s-m-n map, the program running $p$ on the pair of the literal $d$ and its input.
--
--   **Statement.** For every program $p$ and datum $d$,
--
--   $$ |s(p, d)| \;=\; |p| + \mathrm{size}(d) + 35 . $$
--
--   This is the description-size clause of the efficient s-m-n theorem (blueprint `lem:smn`, [MNY, Lemma 2.2]): hardcoding grows a description *additively*. The recursive compression argument relies on it to keep the self-referential description that it hands to the compressor within the size slack of the succinctness definition at the next level, and the compressibility criterion computes the size of its hardcoded search program with this equation.
--
--   **Formalization Note**: The statement is an exact equality, specific to the serialization: `toData (hardcode p d)` is $\mathtt{cons}(\bar 4, \mathtt{cons}(\mathtt{cons}(\bar 2, \mathtt{cons}(\mathtt{cons}(\bar 6, d), \mathtt{cons}(\mathtt{nil},\mathtt{nil}))), \mathrm{enc}(p)))$ with tags $4$ (`let_`), $2$ (`cons`), $6$ (`const`), and $\mathtt{cons}(\mathtt{nil},\mathtt{nil}) = \mathrm{enc}(\mathtt{var}\ 0)$; the $35$ is the node count of this fixed scaffolding. [MNY] states only a polynomial bound on the size of $s(e,x)$.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Toolkit.lean#L94-L99; blueprint lem:smn, https://vidick.github.io/MIPRE-formalization/blueprint/; [MNY] A. Marks, S. S. Nezhadi, H. Yuen, The recursive compression method for proving undecidability results, manuscript, Lemma 2.2

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit

open MIPRE
open MIPRE.Cost
open Polynomial

theorem MIPRE.Cost.hardcode_size (p : Prog) (d : Data) :
    esize (hardcode p d) = esize p + d.size + 35 := by sorry
