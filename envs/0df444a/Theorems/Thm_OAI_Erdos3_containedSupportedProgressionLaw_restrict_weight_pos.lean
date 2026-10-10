-- Prove2me | Theorems.Thm_OAI_Erdos3_containedSupportedProgressionLaw_restrict_weight_pos
-- name    : OAI.Erdos3.containedSupportedProgressionLaw_restrict_weight_pos
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T15:42:15.540868+00:00
-- url     : https://prove2.me/theorems/0e373a15-c778-451c-9039-7423f5b70e95
-- title:
--   Restricting a positive-weight tuple to an axis set keeps positive weight
-- statement:
--   Let $D$ and $\alpha$ be finite types with decidable equality, $B\colon D\to$ Type a family of finite types with decidable equality and $h\colon D\to\mathbb N$; write $\mathcal J=$ `PrincipalTupleIndex B h` $=\Sigma_d\,B(d)\times\mathrm{Fin}\,h(d)$. Let $L,H,\mathrm{step}\colon\mathcal J\to\mathbb N$ and $c\colon\mathcal J\to\mathbb Z$, with $L_j>0$ and $H_j>0$ for all $j$ (`hL`, `hH`) and `integerProgressionSupport (c j) (step j) (H j)` $=\{c_j+\mathrm{step}_j\,i:0\le i<H_j\}\subseteq[0,L_j)$ for all $j$ (`hsubset`). Let $q\in\mathbb N$ and $r\colon\mathcal J\to\mathrm{Option}\,\alpha\to\mathbb Z/q$, and assume (`hcell`) that the event $\{y:$ `principalResidueLabel q y` $=r\}$ (the coordinatewise reduction mod $q$ of $y$ equals $r$) has positive mass under `principalTupleWeights B h H hH`, a `FiniteProbabilityWeights` on `PrincipalIntegerTuples B h α H` (tuples $y$ with $y_j\in[-H_j,H_j)^{\mathrm{Option}\,\alpha}$). Let $\mathrm{law}=$ `containedSupportedProgressionLaw B h L H step c hL hH hsubset q r hcell`, a `FiniteProbabilityWeights` on `PrincipalIntegerTuples B h α L` (the push-forward under `containedProgressionTupleMap` of `principalTupleWeights B h H hH` conditioned on that event). Then for every $y\in$ `PrincipalIntegerTuples B h α L` with $\mathrm{law}(y)>0$ and every predicate $P$ on $D$, the weight of `principalAxisRestrict P y` (the restriction of $y$ to the indices $\langle d,\_\rangle$ with $P(d)$) under `containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell P` (a `FiniteProbabilityWeights` on `PrincipalAxisTuples P L`, the tuples over those indices) is positive.
--
--   Lean: `OAI.Erdos3.containedSupportedProgressionLaw_restrict_weight_pos` in `lean/OAI/Combinatorics/Progressions/Geometry/ContainedSupportedProgressionReference.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B135` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/ContainedSupportedProgressionReference.lean#L29

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B135

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

theorem containedSupportedProgressionLaw_restrict_weight_pos
    (y : PrincipalIntegerTuples B h α L) (hy : 0 < (law).weight y) (P : D → Prop) :
    0 < (containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell P).weight
      (principalAxisRestrict P y) := by
  sorry

end Erdos3
end
end OAI
