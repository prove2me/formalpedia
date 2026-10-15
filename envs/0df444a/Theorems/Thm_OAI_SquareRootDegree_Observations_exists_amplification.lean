-- Prove2me | Theorems.Thm_OAI_SquareRootDegree_Observations_exists_amplification
-- name    : OAI.SquareRootDegree.Observations.exists_amplification
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:57:15.111846+00:00
-- url     : https://prove2.me/theorems/e901ed9b-196b-431d-b145-37c2caafe460
-- title:
--   Grouping and switching amplify the variance of a Boolean-cube observation beyond $(|\mathcal L|+1+\eta)\,n\,\mathrm{Var}(F)$
-- statement:
--   Read a Boolean input as a sign (false is $+1$, true is $-1$), and for a finite coordinate set $\Gamma$ let $\mathcal C_\Gamma=\{-1,1\}^\Gamma$ carry the uniform probability measure. An *observation* is a map $F:\mathcal C_\Gamma\to B$ into a finite label set $B$. Its *score* is the conditional expectation of the coordinate sum given the observed label, and its *variance* is the mean square of the score:
--
--   $$
--   s_F(x)=\mathbb{E}_{x'}\Big[\sum_{k\in\Gamma}x'_k\;\Big|\;F(x')=F(x)\Big],\qquad \mathrm{Var}(F)=\mathbb{E}_x\big[s_F(x)^2\big].
--   $$
--
--   Let $\mathcal L=\{0,1,\dots,2N\}$ with $N=2^{1024}$ be the leaf set and $\eta>0$ the absolute constant of the construction (one half of the Gaussian gain of the leaf tests and selector weights). For a label set $B'$, a selector $S:B'\to\mathcal L$ and a leaf table $L:\mathcal L\times B'\to\{\mathrm{true},\mathrm{false}\}$ define the table event $E_{S,L}\subseteq B'\times(B')^{\mathcal L}$ by: $(y_0,(y_i)_{i\in\mathcal L})\in E_{S,L}$ iff $L(S(y_0),y_{S(y_0)})=\mathrm{false}$ and $L(i,y_i)=\mathrm{true}$ for all $i\ne S(y_0)$. Two constructions are combined.
--
--   1. *Grouping.* For $n\ge1$, the grouped observation $G_n:\mathcal C_{[n]\times\Gamma}\to B^n$ applies $F$ to $n$ disjoint blocks of coordinates, $G_n(x)=\big(F(x_{1,\cdot}),\dots,F(x_{n,\cdot})\big)$.
--   2. *Switching.* Given $S:B^n\to\mathcal L$ and $L:\mathcal L\times B^n\to\{\mathrm{true},\mathrm{false}\}$, the switched observation $W_{n,S,L}$ lives on $|\mathcal L|+2$ disjoint copies of the coordinates of $G_n$: its input consists of an anchor block $z_0$, a block $z_i$ for each leaf $i\in\mathcal L$, and a fresh block $w$, all in $\mathcal C_{[n]\times\Gamma}$. With the old labels $Y=\big(G_n(z_0),(G_n(z_i))_{i\in\mathcal L}\big)$ it outputs, in the disjoint union of $B^n\times(B^n)^{\mathcal L}$ and $B^n$,
--
--   $$
--   W_{n,S,L}(z_0,(z_i)_i,w)=\begin{cases}G_n(w), & Y\in E_{S,L},\\ Y, & Y\notin E_{S,L}.\end{cases}
--   $$
--
--   **Theorem.** If $\mathrm{Var}(F)>0$, then there exist an integer $n\ge1$, a selector $S:B^n\to\mathcal L$ and a leaf table $L:\mathcal L\times B^n\to\{\mathrm{true},\mathrm{false}\}$ such that
--
--   $$
--   n\,\mathrm{Var}(F)\,\big(|\mathcal L|+1+\eta\big)<\mathrm{Var}\big(W_{n,S,L}\big).
--   $$
--
--   For comparison, the observation that always reveals all $|\mathcal L|+1$ old labels has variance $(|\mathcal L|+1)\,n\,\mathrm{Var}(F)$; the theorem says that the switch earns an extra $\eta\,n\,\mathrm{Var}(F)$. If every label cell (fiber indicator) of $F$ has Fourier degree at most $D$, then those of $G_n$ have degree at most $nD$ and those of $W_{n,S,L}$ at most $(|\mathcal L|+1)nD$. So this is the amplification step of the construction: it multiplies the ratio of variance to degree cost by more than the fixed factor $1+\eta/(|\mathcal L|+1)$, and iterating it yields observations whose ratio is arbitrarily large.
--
--   **Formalization Note** Inputs are `Cube γ = γ → Bool`; `score F = conditionalAverage F cubeSum` and `variance F` is the uniform average of its square. Grouping is `grouped (κ := Fin n) F` on `Cube (Fin n × γ)`. Switching is `switched G S L` on `Cube (Slots Leaves × (Fin n × γ))` with `Slots ι = Option (Option ι)` (`none` is the fresh block, `some none` the anchor, `some (some i)` the block of leaf i), and its values lie in `EventSpace (Fin n → β) Leaves ⊕ (Fin n → β)`. Here `Leaves = Fin (2*gridN+1)` with `gridN = (2^128)^8`, so `Fintype.card Leaves` is 2^1025 + 1.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BooleanFunctions/Grouping.lean#L70-L99

import Mathlib
import Definitions.Def_SquareRootDegree
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Walsh
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Conditioning
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Blocks
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Projection
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_FiniteCLT
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Observations
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_SmoothGaussian
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_SmoothSelector
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_GaussianGain
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_MomentTransfer
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_SoftEvent
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Switching
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Rounding
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_CellDegree
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Grouping

open OAI OAI.SquareRootDegree OAI.SquareRootDegree.Observations
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real
open Switching FiniteCLT UniformFinite GaussianGain MomentTransfer
attribute [local instance] Classical.propDecidable
variable {α δ ι : Type*} [Fintype α] [Fintype δ] [Fintype ι]
variable {γ β : Type*} [Fintype γ] [Fintype β] [DecidableEq γ]

omit [Fintype α] [Fintype δ] [Fintype ι] in
theorem OAI.SquareRootDegree.Observations.exists_amplification (F : Cube γ → β) (hv : 0 < variance F) :
    ∃ n : ℕ, 0 < n ∧ ∃ S : (Fin n → β) → Leaves, ∃ L : Leaves → (Fin n → β) → Bool,
      (n:ℝ)*variance F*(Fintype.card Leaves+1+eta) <
        variance (switched (grouped (κ := Fin n) F) S L) := by sorry
