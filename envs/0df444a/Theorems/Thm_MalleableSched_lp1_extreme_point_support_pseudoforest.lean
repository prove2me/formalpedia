-- Prove2me | Theorems.Thm_MalleableSched_lp1_extreme_point_support_pseudoforest
-- name    : MalleableSched.lp1_extreme_point_support_pseudoforest
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:36:03.975541+00:00
-- url     : https://prove2.me/theorems/5ecb20bd-0cfd-4dff-9a5d-9d1f5671b4b6
-- title:
--   Appendix A.3 for (LP1) — the support graph of an extreme point is a pseudoforest
-- statement:
--   Let $\Delta\in\mathbb R^{M\times J}$, let $\mathbf S$ assign machine sets to jobs and let $C\in\mathbb R$. If $x'$ is an extreme point of the feasible region of (LP1), then its support graph $G(x')$, the bipartite graph on $M\cup J$ with an edge $\{i,j\}$ whenever $x'_{ij}>0$, is a **pseudoforest**: every set $A$ of machines and $B$ of jobs spans at most $|A|+|B|$ edges, i.e. every connected component is a tree or contains at most one cycle.
--
--   This is the structural fact of Lenstra, Shmoys and Tardos for the assignment LP of $R\|C_{\max}$, which the paper transfers to (LP1) because the two LPs have the same structure.
--
--   Differences from the source:
--   - reading: Appendix A.3's G, the support graph of an extreme point of the R||Cmax LP (job rows = 1, machine coefficients pᵢⱼ) → G(x′) of (LP1) (job rows ≥ 1, machine coefficients 1/Δᵢⱼ); reason: p.8 says (LP1) has the same structure and that the claim follows from Appendix A.3; every column still has nonzeros only in its job row and its machine row
--   - generalization: Δ from Lemma 4 and C = L(S) → every real matrix Δ, every S : Fin n → Finset (Fin m), every real C; reason: the pseudoforest property uses only the form of the constraints; the paper's instance is a special case
--   - encoding: pseudoforest: every component a tree or with at most one cycle → IsPseudoforest: every machine set A and job set B span at most |A| + |B| edges; reason: equivalent for finite graphs (hereditary counting form)
--   - encoding: decision variables xᵢⱼ only for i ∈ S⁺ⱼ → a full m × n real matrix with xᵢⱼ = 0 for i ∉ S⁺ⱼ; reason: an affine copy of the paper's feasible region; feasible points and extreme points correspond
--   - encoding: job set J and machine set M; set functions on 2^M → Fin n and Fin m (0-based); Finset (Fin m); reason: Lean convention; any finite sets relabel to these
-- source:
--   Fotakis, Matuschke & Papadigenopoulos, Assigning and Scheduling Generalized Malleable Jobs, arXiv:2111.06225v2, Appendix A.3, p.27 ("It can be proved that G is a pseudoforest"), applied to (LP1) on p.8

import Mathlib
import Definitions.Def_MalleableSched_LP1
import Definitions.Def_UnrelatedSched_TwoApprox_DeadlineLP

namespace MalleableSched

open UnrelatedSched.TwoApprox

/-- **The support graph of an extreme point of (LP1) is a pseudoforest.**
Fotakis, Matuschke & Papadigenopoulos, *Assigning and Scheduling Generalized Malleable Jobs
under Subadditive or Submodular Processing Speeds*, arXiv:2111.06225v2, Appendix A.3, p.27, applied to (LP1) on p.8 ("Noting that (LP1) has the same structure
as the assignment LP used for R||Cmax, the following lemma follows from the classic result by
Lenstra et al. (1990); see Appendix A.3"). Appendix A.3, p.27: "It can be proved that G is a
pseudoforest, in the sense that all its connected components are either trees, or contain at most
one cycle."

**Formalization Note.** The support graph `G(x′)` (p.8) is the bipartite machine–job graph with
edge set `supportEdges x = {(i, j) : x i j > 0}`; `IsPseudoforest` is the counting form (every
machine set `A` and job set `B` span at most `|A| + |B|` edges). Stated for every real `Δ`, every
`S` and every real `C`, not only for the paper's `Δ` of Lemma 4 and `C = L(S)`. -/
theorem lp1_extreme_point_support_pseudoforest {n m : ℕ}
    (Δ : Matrix (Fin m) (Fin n) ℝ) (S : Fin n → Finset (Fin m)) (C : ℝ)
    (x : Matrix (Fin m) (Fin n) ℝ) (hx : x ∈ Set.extremePoints ℝ (LP1Region Δ S C)) :
    IsPseudoforest (supportEdges x) := by sorry

end MalleableSched
