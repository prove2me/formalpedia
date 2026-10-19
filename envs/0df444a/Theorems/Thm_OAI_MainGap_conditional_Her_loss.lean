-- Prove2me | Theorems.Thm_OAI_MainGap_conditional_Her_loss
-- name    : OAI.MainGap.conditional_Her_loss
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:34:50.639432+00:00
-- url     : https://prove2.me/theorems/611c3fd6-20e9-41af-ab6e-9d640636692f
-- title:
--   Norm loss $\|pck\|\le\sqrt{1-\delta}\,\|k\|$ on the hereditary subalgebra of $y\,(d-\delta)_+\,y$
-- statement:
--   Let $A$ be a unital C*-algebra, ordered by its cone of positive elements. For $h\in A$ let $\mathrm{Her}(h)=\overline{\{hah^*: a\in A\}}$, and for a self-adjoint $e$ let $(e-\delta)_+$ be the functional-calculus cut-down by $t\mapsto\max(t-\delta,0)$.
--
--   Let $p,y,c\in A$ with $p\ge0$, $y\ge0$, $\|p\|\le1$, $\|y\|\le1$ and $\|c\|\le1$, and let $0\le\delta\le1$. Put
--   $$
--   d=y(1-c^*p^2c)y,\qquad q=y\,(d-\delta)_+\,y .
--   $$
--   Then for every $k\in\mathrm{Her}(q)$,
--   $$
--   \|p\,c\,k\|\ \le\ \sqrt{1-\delta}\;\|k\| .
--   $$
--
--   On the part of $y$ where the defect $d$ exceeds $\delta$, left multiplication by $pc$ loses at least the definite factor $\sqrt{1-\delta}<1$ (for $\delta>0$). This is the loss half of the conditional shrinking step. Combined with the passage from loss bounds to compression constants, it shows that the hereditary subalgebras of a cut-down of $p$ and of $q$ are compressed by $c$ with constant less than $1$.
--
--   **Formalization Note** The algebra carries an arbitrary partial order making it a star-ordered ring, which for a C*-algebra is the usual order. The elements $d$ and $q$ are introduced by `let` in the statement, and $(d-\delta)_+$ is `cut d δ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Compression.lean#L186-L207

import Mathlib
import Definitions.Def_IndividualStrongInfiniteness
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ClosedIdeal
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_PositiveFunctional
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Representation
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Hereditary
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Comparison
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_OrthogonalSlots
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Cutoffs
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ChoicePairs
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_FourChoices
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Defect
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Ultrafilter
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Avoidance
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Graph
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Nonvanishing
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Compression

open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem OAI.MainGap.conditional_Her_loss {p y c : A} (hp : 0 ≤ p) (hy : 0 ≤ y)
    (hpn : ‖p‖ ≤ 1) (hyn : ‖y‖ ≤ 1) (hcn : ‖c‖ ≤ 1)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1) :
    let d := y*(1-star c*(p*p)*c)*y
    let q := y*cut d δ*y
    ∀ k : A, k ∈ Her q → ‖p*c*k‖ ≤ Real.sqrt (1-δ) * ‖k‖ := by sorry
