-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_Path_expand
-- name    : OAI.EuclideanRamsey.Path.expand
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:26:52.085992+00:00
-- url     : https://prove2.me/theorems/3cfc2189-8252-42bd-ab0b-22a4d778feca
-- title:
--   Expanding a weighted path of free-group words into ultrafilter columns of the same weight
-- statement:
--   Let $E=\mathbb{R}^{(\mathbb{N})}$ be the space of finitely supported real sequences with $\langle x,y\rangle=\sum_n x_ny_n$. Let $F$ be the free group on the set $E$, with generator $[z]$ for $z\in E$, and let $\mathcal S$ be the free monoid on $E$ (finite strings of points under concatenation), with $(z)$ the one-letter string. Let $\beta\mathcal S$ be the set of ultrafilters on $\mathcal S$ with the product $A\in U\cdot V\iff\{x:\{y: xy\in A\}\in V\}\in U$; it is a monoid whose identity is the principal ultrafilter at the empty string, and $\delta_\sigma$ denotes the principal ultrafilter at $\sigma\in\mathcal S$.
--
--   Fix an index set $\iota$ and points $a=(a_i)_{i\in\iota}$ in $E$. A family $w=(w_i)_{i\in\iota}$ in $F$ *has a path of weight $\lambda$* if this follows from the rules: every constant family $(g)_{i\in\iota}$ has weight $0$; if $u\ge0$ and $b=(b_i)_{i\in\iota}$ in $E$ satisfies $\|b_i-b_j\|^2=u\,\|a_i-a_j\|^2$ for all $i,j$, then $([b_i])_{i}$ has weight $u$; and if $w$ has weight $\lambda$ and $w'$ has weight $\mu$, then the pointwise product $(w_iw'_i)_i$ has weight $\lambda+\mu$. A *column* is either $\mathrm{com}(U)$ with $U\in\beta\mathcal S$, whose value at every coordinate is $U$, or $\mathrm{pr}(x)$ with $x\in\mathcal S^{\iota}$, whose value at $i$ is $\delta_{x_i}$. *Column paths* are generated in the same way: the empty list and a single common column have weight $0$, the single column $\mathrm{pr}\bigl(i\mapsto(b_i)\bigr)$ with $b$ as above has weight $u$, and concatenation adds weights.
--
--   **Theorem.** Let $w$ have a path of weight $u$. Let $\Psi:F\to\beta\mathcal S$ be multiplicative, $\Psi(gh)=\Psi(g)\cdot\Psi(h)$, and let $p\in\beta\mathcal S$ satisfy $\Psi([z])=p\cdot\delta_{(z)}\cdot p$ for every $z\in E$. Then there is a column path $q_1,\dots,q_n$ of weight $u$ for $a$ such that
--
--   $$
--   q_1(i)\cdot q_2(i)\cdots q_n(i)=\Psi(w_i)\qquad\text{for every } i\in\iota .
--   $$
--
--   This converts a weighted path of free-group words into a list of ultrafilter columns with the same weight, whose coordinatewise products recover the images of the words under $\Psi$. In the Euclidean Ramsey argument $\Psi$ comes from a homomorphism of $F$ into a group sitting inside $\beta\mathcal S$ around an idempotent $p$, and the columns produced here are afterwards realized by actual strings.
--
--   **Formalization Note** $\Psi$ is a multiplicative map `LetterGroup →ₙ* Ultrafilter Strings`, so it need not send $1$ to the identity; the ultrafilter product is Mathlib's `Ultrafilter.mul`, and the products of column values are taken in the monoid `ultrafilterMonoid`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/UltrafilterStrings.lean#L159-L178

import Mathlib
import Definitions.Def_EuclideanRamsey
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Discretization
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_AdicLifting
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorPresentation
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SignedRows
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_FiniteEuclidean
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathFractions
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DerivedFractions
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathWords
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_UltrafilterStrings

open OAI OAI.EuclideanRamsey
universe uModule uIndex uAlpha
open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped BigOperators RealInnerProductSpace
open Filter
open Filter
attribute [local instance] Ultrafilter.mul Ultrafilter.semigroup
variable {ι : Type uIndex}

theorem OAI.EuclideanRamsey.Path.expand {a : ι → FiniteEuclidean} {w u} (h : Path a w u)
    (Ψ : LetterGroup →ₙ* Ultrafilter Strings) (p : Ultrafilter Strings)
    (hgen : ∀ z,Ψ (FreeGroup.of z)=p*(pure (FreeMonoid.of z))*p) :
    ∃ qs : List (UltraColumn ι Strings),ColumnPath a qs u ∧
      (letI := ultrafilterMonoid (M:=Strings); ∀ i,(qs.map (fun q => q.value i)).prod=Ψ (w i)) := by sorry
