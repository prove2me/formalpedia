-- Prove2me | Theorems.Thm_LefebvreVariations_ktaxi_discrepancy_upper_bound
-- name    : LefebvreVariations.ktaxi_discrepancy_upper_bound
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T00:55:52.003826+00:00
-- url     : https://prove2.me/theorems/412863e5-fd14-4230-b2c0-f9e8c44317a6
-- title:
--   Lefebvre's variations, No. 100 — on a theme by k-taxi problem: the oriented discrepancy of a competitive memoryless 2-taxi policy is at most $\rho\,|x-y|$
-- statement:
--   *Lefebvre's variations — posed by Erwan Lefebvre.*
--
--   Let $A$ be a lazy memoryless randomized algorithm for the online 2-taxi problem on $\mathbb{R}$ (its law of the serving location depends only on the multiset of the two taxi positions and the request, and it serves from the pickup when a taxi is already there). Suppose $A$ is oblivious $(\rho,\beta)$-competitive from the start $x_0$: for every finite request list $qs$, $\mathbb{E}\,\mathrm{cost}_A(x_0,qs)\le \rho\,\mathrm{OPT}(x_0,qs)+\beta$, with $\rho\ge1$. For $x,y\in\mathbb{R}$ let $\Delta(x,y)=\sup \mathbb{E}\,\mathrm{cost}_A((x,x),qs)$ over finite request lists $qs$ that can be served at zero cost by an offline algorithm starting from $(x,y)$. Then $\Delta(x,y)\le \rho\,|x-y|$.
--
--   This is the upper half of Coester-Huang-Poon Lemma C.1. The idea is that an additive constant $\beta$ can be amortised away by repeating a zero-cost gadget many times, while the algorithm starts from the symmetric configuration $(x,x)$ and the offline algorithm from $(x,y)$, so that the only unavoidable offline cost is moving the second taxi from $y$ to $x$.
--
--   **Formalization Note** `MemorylessPolicy`, `ObliviousCompetitive`, `discrepancy` are the platform definitions of `Definitions/Def_KTaxi_Competitive_Supplement_Memoryless.lean`; `discrepancy` is an ENNReal supremum (no finiteness assumed), and the statement concludes in ENNReal with `edist`.
--
--   **Why this is a Lefebvre variation.** It is the missing step of a Lean-verified reduction of the open statement `KTaxi.Competitive.Supplement.lemma_C_1` (Coester–Huang–Poon, Lemma C.1, bounds on the oriented discrepancy distance). The reduction proves the lower bound $|x-y| \le \Delta(x,y)$ in Lean and takes this statement as the upper bound $\Delta(x,y) \le \rho|x-y|$. It is one of the two conjuncts of the base statement (a special case of it), and the base statement follows from it together with the proved half.
--
--   **Attribution.** Series *Lefebvre's variations*, posed by Erwan Lefebvre.
-- source:
--   Posed by Erwan Lefebvre (series Lefebvre's variations). J. Coester, C. Huang, Y. Poon, online k-taxi, STOC 2027 submission #96, Appendix C, Lemma C.1 (as formalized on the platform as KTaxi.Competitive.Supplement.lemma_C_1). Origin of this statement: it is the missing step of a reduction of lemma_C_1 (an open milestone of the mission AJOnline.KTaxi2.frontier). The lower bound |x-y| <= discrepancy is proved in the reduction (request (y,y) is free for the offline algorithm from (x,y) and costs the algorithm |x-y| from (x,x)); the upper bound is this statement.

import Mathlib
import Definitions.Def_KTaxi_Competitive_Supplement_Memoryless

set_option autoImplicit false

open scoped ENNReal NNReal

namespace LefebvreVariations

open KTaxi.Competitive.Supplement

theorem ktaxi_discrepancy_upper_bound (A : MemorylessPolicy) (x₀ : Fin 2 → ℝ) (ρ β : ℝ≥0)
    (hρ : 1 ≤ ρ) (hcomp : ObliviousCompetitive A x₀ ρ β) (x y : ℝ) :
    discrepancy A x y ≤ (ρ : ℝ≥0∞) * edist x y := by
  sorry

end LefebvreVariations
