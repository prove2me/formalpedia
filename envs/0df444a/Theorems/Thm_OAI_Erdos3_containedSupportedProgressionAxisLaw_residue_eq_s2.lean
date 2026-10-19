-- Prove2me | Theorems.Thm_OAI_Erdos3_containedSupportedProgressionAxisLaw_residue_eq_s2
-- name    : OAI.Erdos3.containedSupportedProgressionAxisLaw_residue_eq_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:31:15.916359+00:00
-- url     : https://prove2.me/theorems/d31ba9c4-07a8-4248-9103-d234b1cd5d22
-- title:
--   Any two points in the support of the contained supported progression axis law have the same residue label
-- statement:
--   All named objects below are defined by OpenAI. Let $D$ and $\alpha$ be finite types with decidable equality, $B_a$ ($a \in D$) finite types with decidable equality, and $h : D \to \mathbb{N}$. Write $\mathcal{T}$ for `PrincipalTupleIndex B h` (triples $(a, \beta, k)$ with $a \in D$, $\beta \in B_a$, $k < h(a)$). Let $L, H, \mathrm{step} : \mathcal{T} \to \mathbb{N}$ and $c : \mathcal{T} \to \mathbb{Z}$ with $L(t) > 0$ and $H(t) > 0$ for all $t$, and (`hsubset`) for every $t$ the progression `integerProgressionSupport (c t) (step t) (H t)` $= \{c(t) + \mathrm{step}(t)\,k : 0 \le k < H(t)\}$ contained in $[0, L(t))$. Let $q$ be a natural number and $r : \mathcal{T} \to (\texttt{Option}\ \alpha \to \mathbb{Z}/q)$ a residue pattern, such that (`hcell`) the residue cell $\{y : y \bmod q = r\}$ (via `principalResidueLabel q`) has positive mass under `principalTupleWeights B h H hH` (the product over $t$ of OpenAI's integer scalar cube weights with side $H(t)$).
--
--   Let $P$ be a decidable predicate on $D$, and let $u, v$ be elements of `PrincipalAxisTuples P L` (the integer tuples indexed by the triples $(a, \beta, k)$ with $P(a)$, each entry an element of `IntegerScalarCubeBox α (L t)`, i.e. an integer vector indexed by `Option α` with entries in $[-L(t), L(t))$). Suppose both $u$ and $v$ have nonzero weight under `containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell P`, which is the pushforward, under the map $y \mapsto c + \mathrm{step}\cdot y$ (`containedProgressionTupleMap`, applied on the axes with $P$), of the product over those axes of the integer scalar cube weights with side $H$ conditioned on the residue cell $r$. Then `principalResidueLabel q u = principalResidueLabel q v`, i.e. $u$ and $v$ agree entrywise modulo $q$.
--
--   Lean: `OAI.Erdos3.containedSupportedProgressionAxisLaw_residue_eq_s2`, which states OpenAI's `OAI.Erdos3.containedSupportedProgressionAxisLaw_residue_eq` (in `lean/OAI/Combinatorics/Progressions/Lattices/AllocatedSupportedSlicedResidue.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B196` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AllocatedSupportedSlicedResidue.lean (declaration OAI.Erdos3.containedSupportedProgressionAxisLaw_residue_eq)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B196

section

namespace OAI

section

namespace Erdos3
open scoped Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
variable (q : ℕ) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

theorem containedSupportedProgressionAxisLaw_residue_eq_s2 (P : D → Prop) [DecidablePred P]
    (u v : PrincipalAxisTuples (α := α) P L)
    (hu : (containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell P).weight u ≠ 0)
    (hv : (containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell P).weight v ≠ 0) :
    principalResidueLabel q u = principalResidueLabel q v := by
  sorry

end Erdos3

end

end OAI
end
