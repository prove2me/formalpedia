-- Prove2me | Theorems.Thm_MConvexL1_SD_lemma_A_1
-- name    : MConvexL1.SD.lemma_A_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:45:40.996999+00:00
-- url     : https://prove2.me/theorems/08e498ed-448b-468c-8d56-ebc6d12638b7
-- title:
--   Lemma A.1, Appendix A.2, p. 16 — a vector at least as far from x_c moves away from x_c on its support
-- statement:
--   Let $V$ be a finite set and $x_c, y, \tilde y \in \mathbb Z^V$ with $y \ne \tilde y$ and $y(V) = \tilde y(V)$. If $\|y - x_c\|_1 \le \|\tilde y - x_c\|_1$, then
--
--   $$\exists i \in \mathrm{supp}^+(\tilde y - y):\ \tilde y(i) > x_c(i) \qquad\text{or}\qquad \exists j \in \mathrm{supp}^-(\tilde y - y):\ \tilde y(j) < x_c(j)$$
--
--   (or both). The lemma is a purely metric fact about the $\ell_1$ norm on the hyperplane $\{x(V) = \text{const}\}$; it selects the index at which the exchange property is applied in Lemma A.3 and in the proof of Theorem 4.1.
--
--   Differences from the source:
--   - generalization: N = {1, …, n} with n ≥ 2 (§2, p. 4) → an arbitrary finite type V with decidable equality (any cardinality, including 0 and 1); reason: taking V = Fin n with n ≥ 2 gives the paper's setting; for |V| ≤ 1 two distinct vectors cannot have equal sums, so the hypotheses cannot hold and the statement is vacuously true
--   - encoding: ‖x − y‖₁ = Σ |x(i) − y(i)| → L1Dist x y = Σ_v |x v − y v| as a natural number; reason: the norm is a nonnegative integer; same values
-- source:
--   Shioura, M-convex Function Minimization Under L1-Distance Constraint, arXiv:1809.03126v3, Appendix A.2, p. 16, Lemma A.1

import Mathlib
import Definitions.Def_MConvexL1_SD_Basic
import Definitions.Def_DiscreteConvex_MConvexFunctions_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctions_ArgMin
open DiscreteConvex.MConvexFunctions DiscreteConvex.Algorithms

namespace MConvexL1.SD

theorem lemma_A_1 {V : Type*} [Fintype V] [DecidableEq V] (xc y yt : V → ℤ) (hne : y ≠ yt)
    (hsum : ∑ v, y v = ∑ v, yt v) (hdist : L1Dist y xc ≤ L1Dist yt xc) :
    (∃ i ∈ SuppPos yt y, xc i < yt i) ∨ (∃ j ∈ SuppNeg yt y, yt j < xc j) := by sorry

end MConvexL1.SD
