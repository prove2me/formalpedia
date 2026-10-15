-- Prove2me | Theorems.Thm_HiringLP_Parallel_theorem_2
-- name    : HiringLP.Parallel.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:44:56.110709+00:00
-- url     : https://prove2.me/theorems/34ba6ed2-4500-4d3d-8150-0dbd0249f879
-- title:
--   Theorem 2, p. 24 — ALG_par earns at least (1 − 1/e) LP_par(I)
-- statement:
--   Let $I=(k,T,n,p,v)$ be a valid Parallel Offering instance: $1\le k\le T\le n$, $p\in[0,1]^{n\times k}$, $v\in\mathbb R_+^{n\times k}$, and let each candidate's acceptance decisions have marginals $p_{ij}$, possibly correlated across positions and independent across candidates. Let $\mathrm{ALG}_{\mathrm{par}}$ take an optimal solution $y$ of $\mathrm{LP}_{\mathrm{par}}(I)$, round it with a GKPS dependent rounding (P1)–(P3) on the bipartite graph candidates $\times$ positions, put candidate $i$ on the list of position $j$ iff $Y_{ij}=1$, and run all lists in parallel for $T$ rounds, each in decreasing order of $v_{ij}$. Then
--   $$R_{\mathrm{ALG}_{\mathrm{par}}}(I)\ \ge\ \Big(1-\frac1e\Big)\mathrm{LP}_{\mathrm{par}}(I).$$
--
--   Since $\mathrm{LP}_{\mathrm{par}}(I)$ upper-bounds the expected reward of every policy (Lemma 6 of the paper), the non-adaptive policy $\mathrm{ALG}_{\mathrm{par}}$ is a $(1-1/e)$-approximation; the paper shows the factor is tight (App. C.5).
--
--   **Formalization Note** The theorem holds for every rounding distribution with properties (P1)–(P3), which includes the scheme of Gandhi et al. (2006); for every order of each list that is decreasing in $v_{ij}$ (ties in any order); and for every optimal solution $y$, at which the LP objective equals $\mathrm{LP}_{\mathrm{par}}(I)$. $R_{\mathrm{ALG}_{\mathrm{par}}}(I)$ is computed from the run, with the rounding independent of the acceptance decisions.
-- source:
--   Epstein, Ma, Selection and Ordering Policies for Hiring Pipelines via Linear Programming, arXiv:2210.04059v3, p. 24, Theorem 2

import Mathlib
import Definitions.Def_HiringLP_Parallel_Model

namespace HiringLP.Parallel

/-- Theorem 2 (p. 24): for every instance `I ∈ 𝓘_par`, `R_ALG_par(I) ≥ (1 − 1/e) LP_par(I)`.
`ALG_par` solves `LP_par(I)` (optimal solution `y`), rounds `y` with any distribution `μ` having
the GKPS properties (P1)–(P3), puts candidate `i` on the list of position `j` iff `Y_ij = 1`, and
runs the lists in parallel for `T` rounds, each in decreasing order of `v_ij`; the candidates'
acceptance decisions follow `acc`, independent across candidates. -/
theorem theorem_2 {n k : ℕ} (I : Instance n k) (hI : I.Valid)
    (acc : Fin n → Finset (Fin k) → ℝ) (hacc : AccLaw I acc)
    (y : Fin n → Fin k → ℝ) (hopt : IsLPOpt I y)
    (μ : Finset (Fin n × Fin k) → ℝ) (hμ : IsGKPS y μ)
    (ord : Fin k → Equiv.Perm (Fin n)) (hord : IsValueOrder I ord) :
    (1 - Real.exp (-1)) * LPobj I y ≤ algReward I acc μ ord := by sorry

end HiringLP.Parallel
