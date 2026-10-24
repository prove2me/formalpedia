-- Prove2me | Theorems.Thm_MConvexL1_SD_lemma_A_2
-- name    : MConvexL1.SD.lemma_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:45:35.286868+00:00
-- url     : https://prove2.me/theorems/603d64e5-3a58-4952-8b2b-0e142cb6cf15
-- title:
--   Lemma A.2, Appendix A.2, p. 16 — an exchange step does not increase the sum of L1 distances to any point
-- statement:
--   Let $V$ be a finite set, $x, y, z \in \mathbb Z^V$, $i \in \mathrm{supp}^+(x - y)$ and $j \in \mathrm{supp}^-(x - y)$, where $\chi_i$ denotes the $i$-th unit vector. Then
--
--   $$\|x - z\|_1 + \|y - z\|_1 \ \ge\ \|(x - \chi_i + \chi_j) - z\|_1 + \|(y + \chi_i - \chi_j) - z\|_1 .$$
--
--   It says that the map $x \mapsto \|x - z\|_1$ satisfies the exchange inequality (M-EXC) with every admissible $j$; the paper uses it to combine exchanges of $f$ with the $\ell_1$ constraint of (MML1).
--
--   Differences from the source:
--   - generalization: N = {1, …, n} with n ≥ 2 (§2, p. 4) → an arbitrary finite type V with decidable equality (any cardinality, including 0 and 1); reason: taking V = Fin n with n ≥ 2 gives the paper's setting; for |V| ≤ 1 the sets supp⁺(x − y) and supp⁻(x − y) cannot both be nonempty, so the hypotheses cannot hold and the statement is vacuously true
--   - encoding: ‖x − y‖₁ = Σ |x(i) − y(i)| → L1Dist x y = Σ_v |x v − y v| as a natural number; reason: the norm is a nonnegative integer; same values
-- source:
--   Shioura, M-convex Function Minimization Under L1-Distance Constraint, arXiv:1809.03126v3, Appendix A.2, p. 16, Lemma A.2

import Mathlib
import Definitions.Def_MConvexL1_SD_Basic
import Definitions.Def_DiscreteConvex_MConvexFunctions_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctions_ArgMin
open DiscreteConvex.MConvexFunctions DiscreteConvex.Algorithms

namespace MConvexL1.SD

theorem lemma_A_2 {V : Type*} [Fintype V] [DecidableEq V] (x y z : V → ℤ) (i j : V)
    (hi : i ∈ SuppPos x y) (hj : j ∈ SuppNeg x y) :
    L1Dist x z + L1Dist y z ≥
      L1Dist (fun w => x w - CharVec i w + CharVec j w) z +
        L1Dist (fun w => y w + CharVec i w - CharVec j w) z := by sorry

end MConvexL1.SD
