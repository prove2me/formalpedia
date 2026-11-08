-- Prove2me | Theorems.Thm_NNPartTree_lemma_6_4
-- name    : NNPartTree.lemma_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:12:02.64754+00:00
-- url     : https://prove2.me/theorems/e913423b-74bb-409f-b586-876bf98511fc
-- title:
--   Lemma 6.4, p.25 (corrected: corrected oracle, every point of mass $\le\gamma/2$) — $\mathrm{cost}_{\mathcal D}(T)\le 2\gamma+O(\varepsilon_c/\beta_1)$
-- statement:
--   There are absolute constants $c_1,c$ with the following. Let $P$ be injective and $\mathcal D$ a nearest neighbor distribution admitting a perfect $1/3$-balanced halfspace tree $T^\star$. Let $0<\beta_1\le1/3$, $\gamma,\delta\in(0,1)$, $\varepsilon_c>0$, $R\ge c/(\beta_1\gamma)$ and $J\ge c\log(1/(\beta_1\gamma))/\beta_1$, $O$ a $(\beta_1,1/3,R,J,\varepsilon_c)$-balanced cut oracle, and every point of mass at most $\gamma/2$. With blocks of size $m$ as in Claim 6.3, with probability at least $1-\delta$ GreedyTree returns a tree $T$ with
--   $$\mathrm{cost}_{\mathcal D}(T)\le2\gamma+\frac{c\,\varepsilon_c}{\beta_1}.$$
--
--   This is the charging argument: the certificate cuts come from $T^\star$, whose regions are disjoint unions of intersections of halfspaces.
--
--   Differences from the source:
--   - correction: O a balanced cut oracle of Definition 6.5 → the corrected oracle, whose balance holds when some (R, J)-function has balance at least 1/3; reason: Definition 6.5 is unsatisfiable on a point-mass marginal, so the lemma would be vacuous
--   - correction: no condition on point masses → every point has D_nn mass at most γ/2; reason: needed with the corrected oracle, by the counterexample of Claim 6.3; the proof's "every ξ_j ≤ 1/2" fails at a point of mass above η_u/2
--   - encoding: R = O(1/(β₁γ)), J = O(log(1/(β₁γ))/β₁) → all R and J above c/(β₁γ) and c log(1/(β₁γ))/β₁; reason: this includes the smallest such values, and c does not depend on the constant of the oracle, since err(h) = 0 in the proof
--   - encoding: GreedyTree(P, D, δ | O), TestMass on fresh samples → a run on independent blocks indexed by address; failure set of outer measure at most δ; cost in [0, ∞]; reason: each address is tested at most once, so the law is the same
-- source:
--   Khanna, Padaki, Waingarten, Learning Partition Trees for Nearest Neighbor Search, arXiv:2607.09909 (held copy of 2026-11-03, sha256 d32992f2…), Lemma 6.4, p.25; proof pp.25–26

import Mathlib
import Definitions.Def_NNPartTree_GreedyTree

open MeasureTheory

namespace NNPartTree

/-- **Lemma 6.4**, p.25; proof pp.25–26 (corrected). S. Khanna, A. Padaki, E. Waingarten, *Learning Partition Trees for Nearest Neighbor Search*, arXiv:2607.09909 (held copy of 2026-11-03, sha256 d32992f2…).

For a `(β₁, 1/3, R, J, ε_c)`-balanced cut oracle `O` with `R ≥ c/(β₁γ)` and `J ≥ c log(1/(β₁γ))/β₁`, assuming a perfect `1/3`-balanced
halfspace cut tree `T★`, with probability at least `1 − δ` GreedyTree returns a tree `T` with `cost_D(T) ≤ 2γ + c ε_c/β₁`.

**Formalization Note.** The oracle is the corrected one of `IsBalancedCutOracle`, and every point of `P` has mass at most `γ/2`. As printed,
Definition 6.5 is unsatisfiable, so the lemma would be vacuous; and the condition cannot be dropped, by the counterexample in the note of
`claim_6_3`. `T★` is the tree of §1. The constant `c` does not depend on `C_O`: the proof uses `err(h) = 0`. -/
theorem lemma_6_4 : ∃ c₁ c : ℝ, 0 < c₁ ∧ 0 < c ∧
    ∀ (n d : ℕ) (P : Fin n → Pt d), Function.Injective P →
    ∀ (D : Measure (Pt d × Pt d)) [IsProbabilityMeasure D], IsNNDist P D →
    (∃ Tstar : CutTree d, IsPerfectTree P D (1 / 3) Tstar) →
    ∀ (β₁ γ δ ε_c C_O : ℝ) (R J : ℕ) (O : Measure (Pt d × Pt d) → Pt d → ℝ),
    0 < β₁ → β₁ ≤ 1 / 3 → 0 < γ → γ < 1 → 0 < δ → δ < 1 → 0 < ε_c →
    c / (β₁ * γ) ≤ R → c * Real.log (1 / (β₁ * γ)) / β₁ ≤ J →
    IsBalancedCutOracle O β₁ (1 / 3) R J ε_c C_O →
    (∀ i, marginalY D {P i} ≤ ENNReal.ofReal (γ / 2)) →
    ∀ m : ℕ, c₁ * Real.log (1 / (δ * β₁ * γ)) / γ ≤ m →
    m ≤ 2 * (c₁ * Real.log (1 / (δ * β₁ * γ)) / γ) →
    blockLaw D m {ω | ¬ ∃ T : CutTree d, IsGreedyRun O D γ ω T ∧
        cost D T ≤ ENNReal.ofReal (2 * γ + c * ε_c / β₁)} ≤
      ENNReal.ofReal δ := by sorry

end NNPartTree
