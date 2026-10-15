-- Prove2me | Theorems.Thm_OAI_ParityWL_color_indicator_mem_of_separation
-- name    : OAI.ParityWL.color_indicator_mem_of_separation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:53:49.868924+00:00
-- url     : https://prove2.me/theorems/1c758bac-9a3c-4b27-bbf5-9b09ec12e238
-- title:
--   A subalgebra whose colour-invariant elements separate colours contains every colour-class indicator
-- statement:
--   Let $X$ be a finite set, let $D$ be a set with decidable equality, and let $c\colon X\to D$ be a colouring. Let $\mathcal{A}$ be a $\mathbb{Q}$-subalgebra of the algebra $\mathbb{Q}^X$ of all functions $X\to\mathbb{Q}$ with pointwise operations; in particular $\mathcal{A}$ contains the constant function $\mathbf 1$ and is closed under sums, scalar multiples and products. Call $f\in\mathcal{A}$ *colour-invariant* if $c(z)=c(w)$ implies $f(z)=f(w)$.
--
--   **Theorem.** Suppose that colour-invariant elements of $\mathcal{A}$ separate colours: for all $x,y\in X$ with $c(x)\neq c(y)$ there is a colour-invariant $f\in\mathcal{A}$ with $f(x)\neq f(y)$. Then for every $d\in D$ the indicator of the colour class of $d$ belongs to $\mathcal{A}$:
--   $$
--   \mathbf 1_{c=d}\in\mathcal{A},\qquad \mathbf 1_{c=d}(x)=\begin{cases}1,& c(x)=d,\\ 0,& c(x)\neq d.\end{cases}
--   $$
--
--   This is a finite interpolation principle: to show that all colour classes are expressible in an algebra of functions, it suffices to separate any two colours by a colour-invariant element. It is applied with $\mathcal{A}$ the algebra spanned by rooted-test counts and $c$ an atomic type or a Weisfeiler–Leman colour.
--
--   **Formalization Note** The colouring takes values in an arbitrary type `D` with `DecidableEq D`, and $\mathcal{A}$ is a `Subalgebra` of the rational-valued functions on the `Fintype` `X`. If no point has colour $d$ the indicator is the zero function.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ParityLifts/Interpolation.lean#L13-L47

import Mathlib
import Definitions.Def_ParityLifts
import Definitions.Def_OAI_Combinatorics_ParityLifts_LiftCounts
import Definitions.Def_OAI_Combinatorics_ParityLifts_WeightedDual
import Definitions.Def_OAI_Combinatorics_ParityLifts_Masses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BaseLabels
import Definitions.Def_OAI_Combinatorics_ParityLifts_BalancedBags
import Definitions.Def_OAI_Combinatorics_ParityLifts_DecompositionCuts
import Definitions.Def_OAI_Combinatorics_ParityLifts_Witnesses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BagTrees
import Definitions.Def_OAI_Combinatorics_ParityLifts_TagSizes
import Definitions.Def_OAI_Combinatorics_ParityLifts_Detection
import Definitions.Def_OAI_Combinatorics_ParityLifts_RankedTrees
import Definitions.Def_OAI_Combinatorics_ParityLifts_RootedTests
import Definitions.Def_OAI_Combinatorics_ParityLifts_GlueTrees
import Definitions.Def_OAI_Combinatorics_ParityLifts_GlueVertices
import Definitions.Def_OAI_Combinatorics_ParityLifts_Rerooting
import Definitions.Def_OAI_Combinatorics_ParityLifts_TestAlgebra
import Definitions.Def_OAI_Combinatorics_ParityLifts_Interpolation

open OAI OAI.ParityWL
open scoped BigOperators
open scoped Classical

theorem OAI.ParityWL.color_indicator_mem_of_separation {X D : Type} [Fintype X] [DecidableEq D]
    (A : Subalgebra ℚ (X → ℚ)) (c : X → D)
    (hsep : ∀ x y, c x ≠ c y → ∃ f ∈ A,
      (∀ z w, c z = c w → f z = f w) ∧ f x ≠ f y) (d : D) :
    (fun x => if c x = d then (1 : ℚ) else 0) ∈ A := by sorry
