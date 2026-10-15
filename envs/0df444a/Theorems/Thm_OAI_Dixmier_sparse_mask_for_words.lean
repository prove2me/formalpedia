-- Prove2me | Theorems.Thm_OAI_Dixmier_sparse_mask_for_words
-- name    : OAI.Dixmier.sparse_mask_for_words
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:18:13.311628+00:00
-- url     : https://prove2.me/theorems/ad81eb69-0c23-4abf-a5c4-e69353598c90
-- title:
--   Sparse splitting for words of length $\ell$ from a norm bound on $\sum_i R_{s_i}$
-- statement:
--   Let $G$ be a group and let $R$ be its right regular representation on the Hilbert space $\ell^2(G)$ of square-summable functions $G\to\mathbb{C}$, $(R_t\xi)(x)=\xi(xt)$. Let $I$ be a finite set, $s=(s_i)_{i\in I}$ a family of elements of $G$, and $\rho\ge0$ a real number with
--   $$\Bigl\|\sum_{i\in I}R_{s_i}\Bigr\|\le|I|\,\rho.$$
--   For $\ell\in\mathbb{N}$ let $I^\ell$ be the set of words $w=(w_1,\dots,w_\ell)$ of length $\ell$ over $I$, with products $s_w=s_{w_1}s_{w_2}\cdots s_{w_\ell}\in G$, and put $r_\ell=\bigl\lceil|I|^\ell\rho^\ell\bigr\rceil\in\mathbb{N}$. Then for every $\ell\ge1$ there is a mask $a:G\times I^\ell\to\{\mathrm{true},\mathrm{false}\}$ such that for all $x,y\in G$
--   $$\bigl|\{w\in I^\ell:\ a(x,w)=\mathrm{true}\}\bigr|\le r_\ell\qquad\text{and}\qquad\bigl|\{w\in I^\ell:\ a(ys_w^{-1},w)=\mathrm{false}\}\bigr|\le r_\ell.$$
--
--   Think of the $|I|^\ell$ labelled edges $(x,w)$ leaving each $x\in G$, the edge $(x,w)$ ending at $xs_w$. The mask keeps at most $r_\ell$ of the outgoing edges at each vertex on the row side and at most $r_\ell$ of the incoming edges at each vertex on the column side. When $\rho<1$ this is an exponentially small fraction, about $\rho^\ell$, of the $|I|^\ell$ words; in this way a contracting average over finitely many elements of a nonamenable group is turned into sparse masks. Words are distinct labels even when their products coincide.
--
--   **Formalization Note** Words are elements of `Word I ℓ`, the $\ell$-fold iterated product of $I$, with product map `wordProduct s ℓ`; the ceiling is the natural-number ceiling `Nat.ceil`, and the two sets are `rowOnes a x` and `columnZeros a (wordProduct s ℓ) y`. The hypothesis $\rho\ge0$ is part of the statement but is not needed by the proof.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/Regular.lean#L103-L125

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Shrink
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Countable.Small
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_Dixmier
import Definitions.Def_OAI_Analysis_Unitarizability_SparseMask
import Definitions.Def_OAI_Analysis_Unitarizability_EndpointAssignment
import Definitions.Def_OAI_Analysis_Unitarizability_SparseSplitting
import Definitions.Def_OAI_Analysis_Unitarizability_Regular

open OAI OAI.Dixmier
universe u
open Finset
attribute [local instance] Classical.propDecidable
variable {G : Type*}
variable [Group G]

theorem OAI.Dixmier.sparse_mask_for_words {I : Type*} [Fintype I] (s : I → G)
    {ρ : ℝ} (_hρ : 0 ≤ ρ)
    (havg : ‖∑ i, rightRegular (s i)‖ ≤ (Fintype.card I : ℝ) * ρ) (ℓ : ℕ) (hℓ : 0 < ℓ) :
    ∃ a : G → Word I ℓ → Bool,
      (∀ x, (rowOnes a x).card ≤ ⌈(Fintype.card I : ℝ) ^ ℓ * ρ ^ ℓ⌉₊) ∧
      ∀ y, (columnZeros a (wordProduct s ℓ) y).card ≤
        ⌈(Fintype.card I : ℝ) ^ ℓ * ρ ^ ℓ⌉₊ := by sorry
