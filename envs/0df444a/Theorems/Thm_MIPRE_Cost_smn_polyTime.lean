-- Prove2me | Theorems.Thm_MIPRE_Cost_smn_polyTime
-- name    : MIPRE.Cost.smn_polyTime
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:29:14.914418+00:00
-- url     : https://prove2.me/theorems/a0923fc2-0140-4055-983c-acbc8bedc401
-- title:
--   The s-m-n map $(p,a) \mapsto s(p,\mathrm{enc}(a))$ is polynomial-time computable in the model, for any encodable type
-- statement:
--   A *sized encoding* of a type $\alpha$ (`SizedEncoding α`) renders each $a : \alpha$ as a datum $\mathrm{enc}(a)$ of the ambient cost model, with a decoding function inverting it; $|a| := \mathrm{size}(\mathrm{enc}(a))$ (`esize`) is the number of nodes of the encoding. Pairs encode as $\mathrm{enc}(p, a) = \mathtt{cons}(\mathrm{enc}(p), \mathrm{enc}(a))$, so $|(p,a)| = |p| + |a| + 1$, and a program encodes as its tree serialization. A *polynomial-time computable function* $F : \alpha \to \beta$ of the model (`PolyTimeFun α β`) is a function together with a closed program $\mathrm{code}_F$ and an explicit polynomial $T_F \in \mathbb{N}[X]$ such that for every $a$ there is a run $\mathrm{code}_F(\mathrm{enc}(a)) \Downarrow_t \mathrm{enc}(F(a))$ with $t \le T_F(|a|)$, where $p(x) \Downarrow_t r$ denotes a run of the program $p$ on input $x$ with result $r$ at cost $t$. The s-m-n map is $s(p, d) = \mathtt{let}\ \mathtt{cons}(\mathtt{const}\ d, \mathtt{var}\ 0)\ \mathtt{in}\ p$ (`hardcode p d`), the program running $p$ on the pair of the literal $d$ and its input.
--
--   **Statement.** For every type $\alpha$ with a sized encoding there is a polynomial-time computable function $S : \mathrm{Prog} \times \alpha \to \mathrm{Prog}$ of the model such that
--
--   $$ S(p, a) \;=\; s\bigl(p, \mathrm{enc}(a)\bigr) \qquad\text{for all programs } p \text{ and all } a : \alpha . $$
--
--   This is the clause of the efficient s-m-n theorem (blueprint `lem:smn`, [MNY, Lemma 2.2]) that the recursive compression argument uses *at run time*: the self-referential decider must build the hardcoded program $s(\beta, \mathrm{enc}((c', e), 2n+1))$ — the bit-query program $\beta$ with a program, a description and a level hardcoded — while it executes, and does so through this map (`PolyTimeFun.smn`); the compressibility criterion builds its search program the same way. The statement is generic in $\alpha$ because the hardcoded values are programs and tuples, not only bit strings.
--
--   **Formalization Note**: The witness is the definition `PolyTimeFun.smn α`, whose program `smnProg` destructures the encoded pair and assembles the fixed tree of `toData_hardcode` around the two components, running in exactly $|p| + |a| + 38$ steps; its declared time bound is the polynomial $X + 38$, so $T_S(|(p,a)|) = |p| + |a| + 39$. The function is marked `noncomputable` in Lean only because Mathlib's `Polynomial ℕ` is noncomputable data.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Toolkit.lean#L137-L145; blueprint lem:smn, https://vidick.github.io/MIPRE-formalization/blueprint/; [MNY] A. Marks, S. S. Nezhadi, H. Yuen, The recursive compression method for proving undecidability results, manuscript, Lemma 2.2

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

theorem MIPRE.Cost.smn_polyTime (α : Type*) [SizedEncoding α] :
    ∃ S : PolyTimeFun (Prog × α) Prog,
      ∀ (p : Prog) (a : α), S (p, a) = hardcode p (encode a) := by sorry
