-- Prove2me | Theorems.Thm_OAI_Erdos3_containedSupportedProgressionLaw_residue_eq
-- name    : OAI.Erdos3.containedSupportedProgressionLaw_residue_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T11:07:01.913609+00:00
-- url     : https://prove2.me/theorems/cb197e63-15a7-4d4d-88f5-b01215078aaf
-- title:
--   All tuples in the support of the contained supported progression law share one residue label
-- statement:
--   Let $D$ and $\alpha$ be finite types with decidable equality, $B : D\to$ types with each $B_d$ finite with decidable equality, and $h : D\to\mathbb{N}$. Write $\mathcal{J}$ for `PrincipalTupleIndex B h`, the type of triples $(d,b,v)$ with $d\in D$, $b\in B_d$, $v\in\{0,\dots,h_d-1\}$. Let $L,H,\mathrm{step} : \mathcal{J}\to\mathbb{N}$ and $c : \mathcal{J}\to\mathbb{Z}$ with $L_j>0$ and $H_j>0$ for all $j$, and with `integerProgressionSupport (c j) (step j) (H j)` (the set $\{c_j+\mathrm{step}_j\,t : 0\le t<H_j\}$) contained in $\{0,\dots,L_j-1\}$ for all $j$. Let $q$ be a natural number and $r : \mathcal{J}\to\mathrm{Option}\ \alpha\to\mathbb{Z}/q$, and assume the residue cell $\{y : \texttt{principalResidueLabel}\ q\ y=r\}$ has positive mass under `principalTupleWeights B h H hH` (the product over $j$ of OpenAI's uniform laws `integerScalarCubeWeights α (H j)` on integer scalar cubes; `principalResidueLabel q y` is the coordinatewise reduction of $y$ modulo $q$). Let $\lambda$ be `containedSupportedProgressionLaw B h L H step c hL hH hsubset q r hcell`: the push-forward, under the coordinatewise `containedProgressionCubeMap` (sending an integer scalar cube $z$ of size $H_j$ to $i\mapsto[i=\mathrm{none}]\,c_j+\mathrm{step}_j\,z_i$), of `principalTupleWeights B h H hH` conditioned on that residue cell; it is a `FiniteProbabilityWeights` on `PrincipalIntegerTuples B h α L` (families $(y_j)_{j\in\mathcal{J}}$ with $y_j\in$ `IntegerScalarCubeBox α (L j)`). Then for all $y,z$ in `PrincipalIntegerTuples B h α L` with $\lambda.\mathrm{weight}(y)\ne 0$ and $\lambda.\mathrm{weight}(z)\ne 0$,
--   $$\texttt{principalResidueLabel}\ q\ y=\texttt{principalResidueLabel}\ q\ z.$$
--
--   Lean: `OAI.Erdos3.containedSupportedProgressionLaw_residue_eq` in `lean/OAI/Combinatorics/Progressions/Lattices/AllocatedSupportedSlicedResidue.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B012` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AllocatedSupportedSlicedResidue.lean#L42

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B012

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
local notation "weights" => FiniteProbabilityWeights.condition (principalTupleWeights B h H hH)
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell
local notation "law" => containedSupportedProgressionLaw B h L H step c hL hH hsubset q r hcell

theorem containedSupportedProgressionLaw_residue_eq
    (y z : PrincipalIntegerTuples B h α L) (hy : (law).weight y ≠ 0) (hz : (law).weight z ≠ 0) :
    principalResidueLabel q y = principalResidueLabel q z := by
  sorry

end Erdos3
end
end OAI
