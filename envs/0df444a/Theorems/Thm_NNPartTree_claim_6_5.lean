-- Prove2me | Theorems.Thm_NNPartTree_claim_6_5
-- name    : NNPartTree.claim_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:10:17.825852+00:00
-- url     : https://prove2.me/theorems/0d382b04-be6f-485a-a273-a594eb6692b7
-- title:
--   Claim 6.5, p.27 — $k(\varepsilon;R,J;\mathcal D^{(u)})\le k(\gamma\varepsilon/2;R,J;\mathcal D)$ when $u$ has mass at least $\gamma$
-- statement:
--   Let $\mathcal D$ be a law on pairs in $\mathbb R^d\times\mathbb R^d$, and $W$ a measurable set with $\mathcal D_Y(W)\ge\gamma>0$. Let $\mathcal D^{(W)}$ be the conditional mixture. If a polynomial of degree at most $k$ approximates a cut $f$ to $\gamma\varepsilon/2$ under both marginals of $\mathcal D$, then some polynomial of degree at most $k$ approximates $f$ to $\varepsilon$ under both marginals of $\mathcal D^{(W)}$:
--   $$k(\varepsilon;R,J;\mathcal D^{(W)})\le k(\gamma\varepsilon/2;R,J;\mathcal D).$$
--
--   This is what lets the degree hypothesis on $\mathcal D$ apply to every conditional law on which GreedyTree calls its oracle.
--
--   Differences from the source:
--   - generalization: D on ℝ^d × P and W = R_T(u) → any law on pairs and any measurable W with mass at least γ; reason: the proof uses neither restriction, and the printed case is an instance
--   - encoding: inequality between degree functions k(·; R, J; ·) → stated pointwise, for one cut f, one ε and one k; reason: the printed inequality is this statement over all f and ε
--   - encoding: cut f : ℝ^d → {−1, 1} → `IsCut f`, including measurability; ε > 0; reason: a probability needs a measurable function; Definition 5.1 has ε > 0
-- source:
--   Khanna, Padaki, Waingarten, Learning Partition Trees for Nearest Neighbor Search, arXiv:2607.09909 (held copy of 2026-11-03, sha256 d32992f2…), Claim 6.5, p.27

import Mathlib
import Definitions.Def_NNPartTree_CutTree

open MeasureTheory

namespace NNPartTree

/-- **Claim 6.5**, p.27. S. Khanna, A. Padaki, E. Waingarten, *Learning Partition Trees for Nearest Neighbor Search*, arXiv:2607.09909 (held copy of 2026-11-03, sha256 d32992f2…).

If `W` has `D_Y`-mass at least `γ`, then an approximation at `γε/2` under `D` is an approximation at `ε`
of the same degree under the conditional mixture `D^{(u)}`: `k(ε; R, J; D^{(u)}) ≤ k(γε/2; R, J; D)`.

**Formalization Note.** The printed inequality between degree functions is stated pointwise, for one cut
`f` and one degree `k`. `W` is any measurable set, of which `R_T(u)` is a case, and `D` is any law on pairs. -/
theorem claim_6_5 {d : ℕ} (D : Measure (Pt d × Pt d)) [IsProbabilityMeasure D] (W : Set (Pt d))
    (hW : MeasurableSet W) (γ : ℝ) (hγ : 0 < γ) (hmass : ENNReal.ofReal γ ≤ marginalY D W)
    (f : Pt d → ℝ) (hf : IsCut f) (ε : ℝ) (hε : 0 < ε) (k : ℕ)
    (happ : ApproxAt D f (γ * ε / 2) k) : ApproxAt (condMix D W) f ε k := by sorry

end NNPartTree
