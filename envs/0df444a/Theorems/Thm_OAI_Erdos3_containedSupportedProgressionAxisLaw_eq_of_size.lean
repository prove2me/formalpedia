-- Prove2me | Theorems.Thm_OAI_Erdos3_containedSupportedProgressionAxisLaw_eq_of_size
-- name    : OAI.Erdos3.containedSupportedProgressionAxisLaw_eq_of_size
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T15:06:59.517979+00:00
-- url     : https://prove2.me/theorems/bd802dde-e7b6-4ff4-8ab1-ae656ab885fb
-- title:
--   For large progression lengths the axis law equals the contained residue law
-- statement:
--   Let $D$ and $\alpha$ be finite types with decidable equality, $B\colon D\to$ Type a family of finite types with decidable equality and $h\colon D\to\mathbb N$; write $\mathcal J=$ `PrincipalTupleIndex B h` $=\Sigma_d\,B(d)\times\mathrm{Fin}\,h(d)$. Let $L,H,\mathrm{step}\colon\mathcal J\to\mathbb N$ and $c\colon\mathcal J\to\mathbb Z$, with $L_j>0$ and $H_j>0$ for all $j$ (`hL`, `hH`) and `integerProgressionSupport (c j) (step j) (H j)` $=\{c_j+\mathrm{step}_j\,i:0\le i<H_j\}\subseteq[0,L_j)$ for all $j$ (`hsubset`). Let $q>0$ (`hq`) and $r\colon\mathcal J\to\mathrm{Option}\,\alpha\to\mathbb Z/q$, and assume (`hcell`) that the event `principalResidueLabel q y = r` (coordinatewise reduction mod $q$) has positive mass under `principalTupleWeights B h H hH`. Let $P$ be a decidable predicate on $D$; write $B_P$, $h_P$ for the restrictions of $B$, $h$ to $\{d:P(d)\}$, $\iota\colon$ `PrincipalTupleIndex B_P h_P` $\to\mathcal J$ for the inclusion $\langle\langle d,\_\rangle,x\rangle\mapsto\langle d,x\rangle$, and `principalAxisLength P L` $=L\circ\iota$ (similarly for $H$ and step). Assume (`hsize`) $(|\alpha|+1)\,q\le H_{\iota(j)}$ for every $j$. Then `containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell P` equals `containedProgressionResidueLaw B_P h_P (principalAxisLength P L) (principalAxisLength P H) (principalAxisLength P step) (c ∘ ι) (hL ∘ ι) (hH ∘ ι) (hsubset ∘ ι) q hq (r ∘ ι) hsize`. Both are `FiniteProbabilityWeights` on `PrincipalIntegerTuples B_P h_P α (principalAxisLength P L)`: the first is the push-forward under `containedProgressionTupleMap` of the product over $j$ of `principalSupportedCoordinateWeights B h H hH q r hcell (ι j)`, and the second is the push-forward under the same map of `principalResidueWeights` (product weights determined by the residues $r\circ\iota$ mod $q$).
--
--   Lean: `OAI.Erdos3.containedSupportedProgressionAxisLaw_eq_of_size` in `lean/OAI/Combinatorics/Progressions/Geometry/PrincipalCubeSupportedCell.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B135` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/PrincipalCubeSupportedCell.lean#L145

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B135

namespace OAI

section

namespace Erdos3
open scoped Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (P : D → Prop) [DecidablePred P]

local notation "BP" => (fun a : {a // P a} => B (Subtype.val a))
local notation "hP" => (fun a : {a // P a} => h (Subtype.val a))
local notation "embed" => (fun j : PrincipalTupleIndex BP hP => (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j) : PrincipalTupleIndex B h))
local notation "rP" => (fun j : PrincipalTupleIndex BP hP => r (embed j))
local notation "hHP" => (fun j : PrincipalTupleIndex BP hP => hH (embed j))
local notation "conditioned" => FiniteProbabilityWeights.condition (principalTupleWeights B h H hH)
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell

end Erdos3

end

section

namespace Erdos3
open scoped Classical BigOperators

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (P : D → Prop) [DecidablePred P]

local notation "BP" => (fun a : {a // P a} => B (Subtype.val a))
local notation "hP" => (fun a : {a // P a} => h (Subtype.val a))
local notation "embed" => (fun j : PrincipalTupleIndex BP hP => (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j) : PrincipalTupleIndex B h))
local notation "rP" => (fun j : PrincipalTupleIndex BP hP => r (embed j))
local notation "hHP" => (fun j : PrincipalTupleIndex BP hP => hH (embed j))
local notation "conditioned" => FiniteProbabilityWeights.condition (principalTupleWeights B h H hH)
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell

include hq in
theorem containedSupportedProgressionAxisLaw_eq_of_size
    (hsize : ∀ j : PrincipalTupleIndex BP hP, (Fintype.card α + 1) * q ≤ H (embed j)) :
    containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell P =
      containedProgressionResidueLaw BP hP (principalAxisLength P L) (principalAxisLength P H)
        (principalAxisLength P step) (fun j => c (embed j)) (fun j => hL (embed j)) hHP
        (fun j => hsubset (embed j)) q hq rP hsize := by
  sorry

end Erdos3
end
end OAI
