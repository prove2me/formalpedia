-- Prove2me | Theorems.Thm_MultiStageAlloc_Supplement_theorem_2
-- name    : MultiStageAlloc.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:22:29.575028+00:00
-- url     : https://prove2.me/theorems/03c26de8-0125-483b-b396-fb6fd34765d9
-- title:
--   Theorem 2 (Optimal Multi-Stage Algorithm for Configuration Allocation) — PR-MCA is $\Gamma(K)$-competitive
-- statement:
--   For every number of stages $K\ge1$ and every instance $I$ of the $K$-stage fractional configuration allocation problem, with every price on a grid $0=\hat w_0<\hat w_1<\dots<\hat w_T$:
--
--   1. a run of PR-MCA (Algorithm 2) exists, and
--   2. every run of PR-MCA satisfies
--   $$
--   \Gamma(K)\cdot\mathrm{OPT}(I)\ \le\ \mathrm{ALG}(I),\qquad \Gamma(K)=1-\Bigl(1-\frac1K\Bigr)^{K}.
--   $$
--
--   Here $\mathrm{OPT}(I)$ is the optimal value of the offline program PRIMAL-MCA and $\mathrm{ALG}(I)$ the revenue of the run, the total payment for the impressions that are never disposed. A run may choose any optimal solution of the stage program at each stage.
--
--   So PR-MCA is $\Gamma(K)$-competitive. By Theorem 3 no multi-stage algorithm achieves a better ratio even on unweighted matching, a special case of configuration allocation, so $\Gamma(K)$ is the optimal ratio for this problem too.
--
--   **Formalization Note** The competitive ratio of Definition 1 is $\inf_I \mathrm{ALG}(I)/\mathrm{OPT}(I)\ge\Gamma(K)$, which is $0/0$ when $\mathrm{OPT}(I)=0$. The multiplicative form agrees with it whenever $\mathrm{OPT}(I)>0$ and holds trivially otherwise.
--
--   Differences from the source:
--   - reading: “PR-MCA (Algorithm 2) is Γ(K)-competitive”, i.e. inf_I ALG(I)/OPT(I) ≥ Γ(K) (Definition 1) → a run exists, and every run has Γ(K)·OPT(I) ≤ ALG(I); reason: the ratio is 0/0 when OPT(I) = 0, the multiplicative form equals it when OPT(I) > 0, and the stage optimum need not be unique
--   - encoding: advertiser demands n_j in the model of §2.2 → n_j = 1; reason: the paper normalizes n_j = 1 without loss of generality (p.13, footnote 13), and Algorithm 2 and P^MCA_k are defined only for n_j = 1; rescaling ξ ↦ ξ/n_j, w ↦ n_j·w gives an instance with n_j = 1, the same OPT and the same revenue
--   - encoding: prices on the finite grid 0 = ŵ_0 < ŵ_1 < ⋯ < ŵ_T (§4.1 assumption) → the grid is part of the instance and every price equals ŵ_τ for some τ ∈ [T]; reason: the paper's standing assumption of §4.1, which P^MCA_k needs to be defined; the statement holds for every admissible grid
--   - generalization: batches U_k with |U_k| ≥ 1 (§2.1, carried to §2.2 by “similar to our baseline model”) → batches, and the sets U, C, V, may be empty; reason: an empty batch is the same as a batch of one dummy user with ξ ≡ 0 (its x is forced to 0 and its z enters no objective), so every instance of the source is one of the Lean's and the extra instances add nothing the source's instances do not already contain
--   - reading: Algorithm 2's input “convex functions {F_k : [0, 1] → [0, 1]}” → F_k = ∫₀ˣ f_k of Proposition 1 (regF K k), with F_K ≡ 0; reason: the page fixes them by “d/dx F_k(1) = f_k(1) = 1” and “F_K ≡ 0 in the last stage K” (p.28), and the proof (§4.3, Appendix B.7) uses Proposition 1 and Lemma 1 for them
-- source:
--   Feng & Niazadeh, Batching and Optimal Multi-stage Bipartite Allocations, arXiv:2211.16581v1, Theorem 2, p.26 (proof §4.3, pp.29–30, and Appendix B.7)

import Mathlib
import Definitions.Def_MultiStageAlloc_Supplement_PrimalMCA
import Definitions.Def_MultiStageAlloc_Supplement_RunMCA

namespace MultiStageAlloc.Supplement

/-- **Theorem 2 (Optimal Multi-Stage Algorithm for Configuration Allocation).** Feng & Niazadeh,
*Batching and Optimal Multi-stage Bipartite Allocations*, arXiv:2211.16581v1, p.26. In the
`K`-stage (fractional) configuration allocation problem, PR-MCA (Algorithm 2) is
`Γ(K)`-competitive, where `Γ(K) = 1 - (1 - 1/K)^K`: for every `K ≥ 1` and every instance (with its
price grid), a run of Algorithm 2 exists, and every run has `Γ(K) · OPT(I) ≤ ALG(I)`, where `OPT` is
the value of PRIMAL-MCA and `ALG` the revenue of the run.

**Formalization Note.** Definition 1's `inf ALG(I)/OPT(I) ≥ α` (p.14) is `0/0` when `OPT(I) = 0`; the
multiplicative form equals it on `OPT(I) > 0` and holds trivially otherwise. Capacities are
`n_j = 1` and prices lie on the grid of §4.1, as in the paper. "Every run" covers every choice of
optimal solution at every stage. -/
theorem theorem_2 {U C V : Type*} [Fintype U] [Fintype C] [Fintype V] (K : ℕ) (hK : 1 ≤ K)
    (I : MCAInstance U C V K) :
    (∃ x y z η, IsMCARun I x y z η) ∧
      ∀ x y z η, IsMCARun I x y z η → gammaK K * mcaOPT I ≤ mcaALG I x y η := by sorry

end MultiStageAlloc.Supplement
