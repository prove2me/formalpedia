-- Prove2me | Theorems.Thm_OAI_Erdos3_exists_containedSupportedProgressionReference_s2
-- name    : OAI.Erdos3.exists_containedSupportedProgressionReference_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:34:09.534359+00:00
-- url     : https://prove2.me/theorems/5f8f3bd2-47cd-4d37-a101-50fe5e5e9198
-- title:
--   A reference tuple for the contained supported progression law
-- statement:
--   Let $D$ and $\alpha$ be finite types with decidable equality, $B(a)$ for $a \in D$ finite types with decidable equality, and $h : D \to \mathbb{N}$. The principal tuple index is $\mathrm{PrincipalTupleIndex}\ B\ h = \Sigma_{a \in D} B(a) \times \{0,\dots,h(a)-1\}$. Let $L, H, \mathrm{step}$ be natural-valued and $c$ integer-valued functions on this index set, with $L(j) > 0$, $H(j) > 0$ and the progression `integerProgressionSupport (c j) (step j) (H j)` ($= \{c(j) + \mathrm{step}(j)\, k : 0 \le k < H(j)\}$) contained in $[0, L(j))$ for every $j$. Let $q$ be a natural number and $r$ a function assigning to each index $j$ a residue vector $\texttt{Option}\ \alpha \to \mathbb{Z}/q$, such that the residue cell $\{y : \texttt{principalResidueLabel q}\ y = r\}$ has positive mass under `principalTupleWeights B h H hH` (the product over $j$ of the cube laws `integerScalarCubeWeights α (H j)`; `principalResidueLabel q y` is the coordinatewise reduction of $y$ modulo $q$). Let `law` = `containedSupportedProgressionLaw B h L H step c hL hH hsubset q r hcell`, OpenAI's finite probability law on `PrincipalIntegerTuples B h α L` (tuples $y$ with $y_j$ in `IntegerScalarCubeBox α (L j)`, i.e. a map from `Option α` to integers in $[-L(j), L(j))$), obtained by conditioning on the residue cell and mapping the cube of side $H(j)$ onto the progression inside the cube of side $L(j)$.
--
--   Then there exists a tuple $y_0 \in$ `PrincipalIntegerTuples B h α L` such that:
--   1. $y_0$ has positive weight under `law`;
--   2. for every index $j$, `IntegerScalarCube (L j) (y₀ j)` holds (OpenAI: every cube vertex value of $y_0(j)$, one for each subset of $\alpha$, lies in $[0, L(j))$);
--   3. for every predicate $P$ on $D$, the restriction `principalAxisRestrict P y₀` of $y_0$ to the indices whose axis satisfies $P$ has positive weight under the axis law `containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell P`;
--   4. every tuple $y$ with nonzero weight under `law` has the same residue label as $y_0$: $\texttt{principalResidueLabel q}\ y = \texttt{principalResidueLabel q}\ y_0$.
--
--   Lean: `OAI.Erdos3.exists_containedSupportedProgressionReference_s2`, which states OpenAI's `OAI.Erdos3.exists_containedSupportedProgressionReference` (in `lean/OAI/Combinatorics/Progressions/Geometry/ContainedSupportedProgressionReference.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B196` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/ContainedSupportedProgressionReference.lean (declaration OAI.Erdos3.exists_containedSupportedProgressionReference)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B196

section

namespace OAI

section

namespace Erdos3
open scoped Classical BigOperators

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
variable (q : ℕ) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
local notation "law" => containedSupportedProgressionLaw B h L H step c hL hH hsubset q r hcell

theorem exists_containedSupportedProgressionReference_s2 :
    ∃ y₀ : PrincipalIntegerTuples B h α L,
      0 < (law).weight y₀ ∧
      (∀ j, IntegerScalarCube (L j) (fun a => (y₀ j a : ℤ))) ∧
      (∀ P : D → Prop,
        0 < (containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell P).weight
          (principalAxisRestrict P y₀)) ∧
      (∀ y, (law).weight y ≠ 0 → principalResidueLabel q y = principalResidueLabel q y₀) := by
  sorry

end Erdos3

end

end OAI
end
