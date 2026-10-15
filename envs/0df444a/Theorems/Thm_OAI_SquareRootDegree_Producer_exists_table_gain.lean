-- Prove2me | Theorems.Thm_OAI_SquareRootDegree_Producer_exists_table_gain
-- name    : OAI.SquareRootDegree.Producer.exists_table_gain
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:56:48.123538+00:00
-- url     : https://prove2.me/theorems/fc0dbc1e-ecfa-400b-8816-82e5503bcce6
-- title:
--   A deterministic leaf-table event on label tuples with deficit above $\eta$
-- statement:
--   Let $\alpha$ be a finite nonempty set and $\beta$ a finite set; every average $\mathbb{E}$ below is taken with respect to the uniform probability measure on a finite set. Let $F:\alpha\to\beta$ be a labelling map and $t:\beta\to\mathbb{R}$ a score on labels whose pull-back $t\circ F$ is standardized:
--
--   $$
--   \mathbb{E}_{a\in\alpha}\,t(F(a))=0,\qquad \mathbb{E}_{a\in\alpha}\,t(F(a))^2=1.
--   $$
--
--   The following data are fixed once and for all and do not depend on $F$ or $t$: the leaf set $\mathcal L=\{0,1,\dots,2N\}$ with $N=2^{1024}$ (so $|\mathcal L|=2N+1$), and the absolute constant $\eta>0$ of the construction, defined as one half of the "Gaussian gain" of the leaf tests and selector weights. For $n\ge1$ and $x=(x_1,\dots,x_n)\in\alpha^n$ write
--
--   $$
--   T_n(x)=\frac{1}{\sqrt n}\sum_{j=1}^{n}t(F(x_j)),\qquad F^{(n)}(x)=\big(F(x_1),\dots,F(x_n)\big)\in\beta^n .
--   $$
--
--   A *selector* $S:\beta^n\to\mathcal L$ and a *leaf table* $L:\mathcal L\times\beta^n\to\{\mathrm{true},\mathrm{false}\}$ determine the *table event* $E_{S,L}\subseteq\beta^n\times(\beta^n)^{\mathcal L}$: a tuple $(y_0,(y_i)_{i\in\mathcal L})$ belongs to $E_{S,L}$ if and only if, with $s=S(y_0)$, the selected leaf rejects its own sample, $L(s,y_s)=\mathrm{false}$, while every other leaf accepts its sample, $L(i,y_i)=\mathrm{true}$ for all $i\neq s$.
--
--   **Theorem.** There exist an integer $n\ge1$, a real number $b$, a selector $S:\beta^n\to\mathcal L$ and a leaf table $L:\mathcal L\times\beta^n\to\{\mathrm{true},\mathrm{false}\}$ such that
--
--   $$
--   \eta<\mathbb{E}\Big[\mathbf 1\big\{\big(F^{(n)}(x_0),(F^{(n)}(x_i))_{i\in\mathcal L}\big)\in E_{S,L}\big\}\Big(1-\Big(T_n(x_0)+\sum_{i\in\mathcal L}T_n(x_i)-b\Big)^2\Big)\Big],
--   $$
--
--   where $x_0$ and $x_i$ ($i\in\mathcal L$) are independent uniformly random points of $\alpha^n$. The right-hand side is the *deficit* of the event at shift $b$.
--
--   The event is deterministic, it depends on the $1+|\mathcal L|$ samples only through their labels, and the threshold $\eta$ is uniform in $F$ and $t$. The deficit has a prediction meaning: for one more independent sample $w$, it equals one minus the mean squared error of predicting $T_n(x_0)+\sum_i T_n(x_i)+T_n(w)$ by the old sum $T_n(x_0)+\sum_iT_n(x_i)$ off the event and by $b+T_n(w)$ on the event. A deficit above $\eta$ is therefore exactly what the switching construction needs in order to gain a fixed multiplicative amount of variance when an observation is amplified.
--
--   **Formalization Note** The deficit is `SoftEvent.deficit (normalizedSum (fun a => t (F a)) n) b a`, a uniform average over `(Fin n → α) × (Leaves → Fin n → α)` with `Leaves = Fin (2*gridN+1)` and `gridN = (2^128)^8`; the event weight `a` is `if TableRounding.tableEvent S L (labels) then 1 else 0`, and `eta = gain gaussianLeafMoments gaussianSelectorMoments / 2`. The `MeasurableSpace` and `MeasurableSingletonClass` instances on `α` are only there to state the central limit theorem used in the proof; they do not change the statement.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BooleanFunctions/Producer.lean#L72-L94

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

open OAI OAI.SquareRootDegree
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real
open MeasureTheory ProbabilityTheory Filter UniformFinite FiniteCLT MomentTransfer GaussianGain
open scoped Topology
attribute [local instance] Classical.propDecidable
variable {α β : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]

theorem OAI.SquareRootDegree.Producer.exists_table_gain [Fintype β] (F : α → β) (t : β → ℝ)
    (h0 : average (fun a => t (F a)) = 0)
    (h1 : average (fun a => (t (F a))^2) = 1) :
    ∃ n : ℕ, 0 < n ∧ ∃ b : ℝ, ∃ S : (Fin n → β) → Leaves,
      ∃ L : Leaves → (Fin n → β) → Bool,
      eta < SoftEvent.deficit (normalizedSum (fun a => t (F a)) n) b
        (fun x => if TableRounding.tableEvent S L
          ((fun j => F (x.1 j)),fun i j => F (x.2 i j)) then 1 else 0) := by sorry
