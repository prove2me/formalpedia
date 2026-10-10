-- Prove2me | Theorems.Thm_OAI_Erdos3_principalAffineIntervalLaw_axis_contained_complexMean
-- name    : OAI.Erdos3.principalAffineIntervalLaw_axis_contained_complexMean
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T14:48:00.395001+00:00
-- url     : https://prove2.me/theorems/dd961987-676d-4346-990a-b8a17b89d5f4
-- title:
--   Splitting the mean of the principal affine interval law along an axis set
-- statement:
--   Let $D$ be a finite type with decidable equality, $B\colon D\to$ Type a family of finite types with decidable equality and $h\colon D\to\mathbb N$; write $\mathcal J=$ `PrincipalTupleIndex B h` $=\Sigma_d\,B(d)\times\mathrm{Fin}\,h(d)$. Let $L,H,\mathrm{step}\colon\mathcal J\to\mathbb N$ and `start` $\colon\mathcal J\to\mathbb Z$ with $0\le\mathrm{start}_j+\mathrm{step}_j\,t<L_j$ for all $j$ and $t<H_j$ (`hinside`) and $H_j>0$ for all $j$ (`hH`), and let $P$ be a predicate on $D$. Write $\mathcal J'$ for `PrincipalTupleIndex` of the restrictions of $B$ and $h$ to $\{d:\neg P(d)\}$, $\iota\colon\mathcal J'\to\mathcal J$ for the inclusion, and `principalAxisLength (¬P) L` $=L\circ\iota$ (similarly for $H$, step). Assume $L_{\iota(j)}>0$ (`hL`) and `integerProgressionSupport (start (ι j)) (step (ι j)) (H (ι j))` $\subseteq[0,L_{\iota(j)})$ (`hsubset`) for all $j\in\mathcal J'$. Then for every $f\colon$ `PrincipalIntegerTuples B h Empty L` $\to\mathbb C$,
--   $$\mathbb E_{\texttt{principalAffineIntervalLaw}}[f]=\mathbb E_{u\sim\texttt{principalAffineIntervalAxisLaw}\ P}\Big[\ \mathbb E_{v\sim W'}\big[f(\texttt{principalAxisJoin}\ P\ u\ (\texttt{containedProgressionTupleMap}\ \ldots\ \mathrm{hL}\ \mathrm{hsubset}\ v))\big]\Big],$$
--   where $\mathbb E$ is `complexMean` ($\sum_x w(x)\,g(x)$ for weights $w$); `principalAffineIntervalLaw B h L H step start hinside hH` is the `FiniteProbabilityWeights` on `PrincipalIntegerTuples B h Empty L` obtained by pushing the uniform distribution on $\prod_j\mathrm{Fin}\,H_j$ forward under `principalAffineIntervalPoint`; `principalAffineIntervalAxisLaw … P` is its push-forward under `principalAxisRestrict P` (restriction to the indices over $P$); $W'=$ `principalTupleWeights` (with $\alpha=$ Empty) of the restricted families with lengths $H\circ\iota$, a `FiniteProbabilityWeights` on tuples over $\mathcal J'$; `containedProgressionTupleMap` is applied with the restricted families, lengths $L\circ\iota$, $H\circ\iota$, strides $\mathrm{step}\circ\iota$ and starts $\mathrm{start}\circ\iota$, mapping such tuples into `PrincipalIntegerTuples` with lengths $L\circ\iota$; and `principalAxisJoin P u v` is the tuple equal to $u$ at indices over $P$ and to $v$ elsewhere.
--
--   Lean: `OAI.Erdos3.principalAffineIntervalLaw_axis_contained_complexMean` in `lean/OAI/Combinatorics/Progressions/Lattices/AllocatedSupportedSlicedResidue.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B135` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AllocatedSupportedSlicedResidue.lean#L446

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B135

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

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

variable {D : Type*} [Fintype D] [DecidableEq D]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (h : D → ℕ)
variable (H : PrincipalTupleIndex B h → ℕ) (hH : ∀ j, 0 < H j)

variable (L step : PrincipalTupleIndex B h → ℕ) (start : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j)
variable (hinside : ∀ j (t : Fin (H j)),
  0 ≤ start j + (step j : ℤ) * t.val ∧ start j + (step j : ℤ) * t.val < L j)
variable (hsubset : ∀ j, integerProgressionSupport (start j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

variable {D : Type*} [Fintype D] [DecidableEq D]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (start : PrincipalTupleIndex B h → ℤ)
variable (hinside : ∀ j (t : Fin (H j)),
  0 ≤ start j + (step j : ℤ) * t.val ∧ start j + (step j : ℤ) * t.val < L j)
variable (hH : ∀ j, 0 < H j) (P : D → Prop)

theorem principalAffineIntervalLaw_axis_contained_complexMean
    (hL : ∀ j : PrincipalTupleIndex (fun d : {d // ¬P d} => B d.val) (fun d => h d.val),
      0 < principalAxisLength (fun d => ¬P d) L j)
    (hsubset : ∀ j : PrincipalTupleIndex (fun d : {d // ¬P d} => B d.val) (fun d => h d.val),
      integerProgressionSupport (start ⟨j.1.val, j.2⟩)
        (principalAxisLength (fun d => ¬P d) step j : ℤ)
        (principalAxisLength (fun d => ¬P d) H j) ⊆
      Finset.Ico (0 : ℤ) (principalAxisLength (fun d => ¬P d) L j : ℤ))
    (f : PrincipalIntegerTuples B h Empty L → ℂ) :
    (principalAffineIntervalLaw B h L H step start hinside hH).complexMean f =
      (principalAffineIntervalAxisLaw B h L H step start hinside hH P).complexMean (fun u =>
      (principalTupleWeights (α := Empty) (fun d : {d // ¬P d} => B d.val) (fun d => h d.val)
        (principalAxisLength (fun d => ¬P d) H) (fun j => hH ⟨j.1.val, j.2⟩)).complexMean
        (fun v => f (principalAxisJoin P u
          (containedProgressionTupleMap (fun d : {d // ¬P d} => B d.val) (fun d => h d.val)
            (principalAxisLength (fun d => ¬P d) L) (principalAxisLength (fun d => ¬P d) H)
            (principalAxisLength (fun d => ¬P d) step) (fun j => start ⟨j.1.val, j.2⟩)
            hL hsubset v)))) := by
  sorry

end Erdos3
end
end OAI
