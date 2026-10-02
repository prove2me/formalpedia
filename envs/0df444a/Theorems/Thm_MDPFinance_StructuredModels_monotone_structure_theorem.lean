-- Prove2me | Theorems.Thm_MDPFinance_StructuredModels_monotone_structure_theorem
-- name    : MDPFinance.StructuredModels.monotone_structure_theorem
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T21:38:23.804268+00:00
-- url     : https://prove2.me/theorems/db359729-38ff-41e9-b315-1d98b7f8d613
-- title:
--   Theorem 2.4.14 — the monotone structure theorem
-- statement:
--   Suppose a Markov Decision Model $M$ with upper bounding function $b$ satisfies, for every
--   stage $n = 0,\dots,N-1$: (i) $D_n(\cdot)$ is increasing ($x \leq x' \Rightarrow D_n(x)
--   \subseteq D_n(x')$); (ii) $x \mapsto \int v(x')\,Q_n(dx' \mid x,a)$ is increasing for every
--   increasing $v \in \mathbb{I\!B}_b^+$ and every admissible $a$; (iii) $x \mapsto r_n(x,a)$ is
--   increasing for every $a$; (iv) $g_N$ is increasing; (v) every increasing $v \in
--   \mathbb{I\!B}_b^+$ has a maximizer in $\Delta_n$. Then
--
--   $$
--   \mathrm{I\!M}_n := \{v \in \mathbb{I\!B}_b^+ : v \text{ increasing}\}, \qquad (\Delta_n)_{n<N}
--   $$
--
--   satisfy the Structure Assumption (SAN).
--
--   **Formalization Note.** $E$, $A$ carry only a `Preorder` (no vector-space structure): this
--   theorem needs monotonicity, not convexity. $\Delta_n$ is left as an arbitrary parameter,
--   exactly the set hypothesis (v) quantifies over, matching the book's own statement (it is not
--   fixed in advance to "weakly increasing decision rules" — that specialization appears only
--   after Proposition 2.4.16, as a corollary).
--
--   **Formalization Note (moderation).** In (ii) and (iii) the maps $x \mapsto \int v\,dQ_n(\cdot
--   \mid x,a)$ and $x \mapsto r_n(x,a)$ are required to be increasing on their domain $\{x : a \in
--   D_n(x)\}$ (an up-set by (i)), where $Q_n$ and $r_n$ are defined, not on all of $E$ through
--   values outside $D_n$ that the model does not constrain.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 35, Theorem 2.4.14

import Mathlib
import Definitions.Def_MDPFinance_StructuredModels_Model
import Definitions.Def_MDPFinance_StructuredModels_Policy
import Definitions.Def_MDPFinance_StructuredModels_Operators
import Definitions.Def_MDPFinance_StructuredModels_BoundingFunction
import Definitions.Def_MDPFinance_StructuredModels_StructureAssumption

open MeasureTheory ProbabilityTheory

namespace MDPFinance.StructuredModels

/-- Theorem 2.4.14 (Bäuerle–Rieder, p. 35, PDF 50). Suppose a Markov Decision Model with upper
bounding function `b` is given and for all `n = 0, …, N-1` it holds: (i) `D_n(·)` is increasing,
i.e. `x ≤ x'` implies `D_n(x) ⊂ D_n(x')`; (ii) the stochastic kernels `Q_n(·|x,a)` are
stochastically monotone for all `a ∈ D_n(x)`, i.e. `x ↦ ∫ v(x') Q_n(dx'|x,a)` is increasing for
all increasing `v ∈ IB_b^+` and for all `a ∈ D_n(x)`; (iii) `x ↦ r_n(x,a)` is increasing for all
`a`; (iv) `g_N` is increasing on `E`; (v) for all increasing `v ∈ IB_b^+` there exists a
maximizer `f_n ∈ Δ_n` of `v`. Then the sets `IM_n := {v ∈ IB_b^+ | v increasing}` and `Δ_n`
satisfy the Structure Assumption (SAN). In (ii) and (iii) the maps `x ↦ ∫ v dQ_n(·|x,a)` and
`x ↦ r_n(x,a)` are increasing on their domain `{x | a ∈ D_n(x)}` (an up-set by (i)), where `Q_n` and
`r_n` are defined. -/
theorem monotone_structure_theorem {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]
    [Preorder E] [Preorder A] {N : ℕ} (M : MarkovDecisionModel E A N) (b : E → ℝ)
    (cr cg αb : ℝ) (hb : IsUpperBoundingFunction M b cr cg αb) (Deltas : ℕ → Set (E → A))
    (hD : ∀ n < N, Monotone (M.Dx n))
    (hQ : ∀ n < N, ∀ a, ∀ v ∈ IBbPlus b, Monotone v →
      MonotoneOn (fun x' => erealIntegral (M.Q n (x', a)) v) {x' | a ∈ M.Dx n x'})
    (hr : ∀ n < N, ∀ a, MonotoneOn (fun x => M.r n (x, a)) {x | a ∈ M.Dx n x})
    (hg : Monotone M.g)
    (hmax : ∀ n < N, ∀ v ∈ IBbPlus b, Monotone v → ∃ f ∈ Deltas n, IsMaximizer M n v f) :
    StructureAssumption M (fun n => {v ∈ IBbPlus b | Monotone v}) Deltas := by sorry

end MDPFinance.StructuredModels
