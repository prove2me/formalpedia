-- Prove2me | Theorems.Thm_FracTruthSched_lemma_5
-- name    : FracTruthSched.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:34:17.655423+00:00
-- url     : https://prove2.me/theorems/e652f497-554c-479a-97fc-7b389e9fc315
-- title:
--   Lemma 5 — a common leaf value $\lambda\in(1,1+\varepsilon)$ with additivity and symmetry within classes
-- statement:
--   Let $\ell\ge2$ and let $(x,P)$ be a feasible truthful mechanism on the graph inputs of $MC_\ell$ with eligibility (i), zero-type irrelevance (iii) and symmetry (iv). Fix a root $i$ and $\varepsilon>0$. Give every core edge not incident to $i$ value zero at both endpoints, and every self-loop owner value zero. Let $D_j=Q_{\{i,j\}}$, $j\ne i$, be the $\ell$-edge classes incident to $i$.
--
--   There is $\lambda\in(1,1+\varepsilon)$ with the following property. When every opposing endpoint value in these classes equals $\lambda$, the root's disutility function $V$ (a function of its values on its incident edges) is additive within each $D_j$, for every fixed choice of the root's values on the other classes, and it is symmetric under permutations of the coordinates within each $D_j$.
--
--   This lemma supplies the additivity and symmetry required by fixed-star retention (Lemma 3) without any continuity assumption.
--
--   Differences from the source:
--   - generalization: a limit mechanism on MC_ℓ (Definition 6: the mechanism constructed in Lemma 1) → every feasible truthful mechanism on the graph inputs of MC_ℓ with eligibility (i), zero-type irrelevance (iii) and symmetry (iv); reason: the proof uses Lemma 4, Lemma 2 (b) and property (iv); every limit mechanism has these properties by Lemma 1, so the statement specializes to the source's
--   - encoding: a graph input of MC_ℓ: the two endpoint values of every edge and the owner value of every self-loop, all nonnegative, and no other values → t : Fin n → CoreTask n ℓ → ℝ, nonnegative and 0 at every (machine, task) pair that is not incident (IsGraphInput); edges of Q{u,v} are encoded with u < v; reason: a machine's cost Σ_e t_ie x_ie is then its cost on its incident tasks; same inputs and same costs
-- source:
--   Anastasiadis et al., Tight bounds for fractional and randomized truthful scheduling, arXiv:2611.06642v1, Lemma 5, p.17

import Mathlib
import Definitions.Def_FracTruthSched_IsFeasibleOn
import Definitions.Def_FracTruthSched_IsTruthfulOn
import Definitions.Def_FracTruthSched_IsGraphInput
import Definitions.Def_FracTruthSched_IsEligible
import Definitions.Def_FracTruthSched_HasZeroTypeIrrelevance
import Definitions.Def_FracTruthSched_IsClassSymmetric
import Definitions.Def_FracTruthSched_rootStarInput
import Definitions.Def_FracTruthSched_classSet
import Definitions.Def_FracTruthSched_IsAdditiveOn
import Definitions.Def_FracTruthSched_IsSymmetricOn

set_option autoImplicit false

namespace FracTruthSched

/-- **Lemma 5 (common leaf value)** (Anastasiadis et al., arXiv:2611.06642v1, Lemma 5, p.17). Fix a
root `i` and `ε > 0`. Give every core edge not incident to `i` value zero at both endpoints, and every
self-loop owner value zero. Let `D_1, …, D_k` be the `ℓ`-edge classes incident to `i`. There is
`λ ∈ (1, 1 + ε)` such that, when every opposing endpoint value in these classes equals `λ`, the root's
disutility function `V` is additive within each `D_j`, for every fixed choice of the root's values on
the other classes, and symmetric under permutations of the coordinates within each `D_j`.

**Formalization Note.** Stated for every feasible truthful mechanism on `MC_ℓ` with (i), (iii) and
(iv), the properties the proof uses (every limit mechanism has them). `V(a)` is the root's disutility
at `rootStarInput i λ a` (root values `a` on its incident edges, opposing values `λ`, all else `0`,
the root's own self-loop included); `D_j = classSet i j`, `j ≠ i`. -/
theorem lemma_5 {n ℓ : ℕ} (hℓ : 2 ≤ ℓ) (M : FracMech n (CoreTask n ℓ))
    (hfeas : IsFeasibleOn IsGraphInput M) (htruth : IsTruthfulOn IsGraphInput M)
    (hel : IsEligible M) (hzti : HasZeroTypeIrrelevance M) (hsym : IsClassSymmetric M)
    (i : Fin n) (ε : ℝ) (hε : 0 < ε) :
    ∃ lam ∈ Set.Ioo 1 (1 + ε), ∀ j, j ≠ i →
      IsAdditiveOn (fun a => disutility M (rootStarInput i lam a) i) (classSet i j) ∧
        IsSymmetricOn (fun a => disutility M (rootStarInput i lam a) i) (classSet i j) := by sorry

end FracTruthSched
