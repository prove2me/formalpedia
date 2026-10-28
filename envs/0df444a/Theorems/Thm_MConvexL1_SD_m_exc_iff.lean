-- Prove2me | Theorems.Thm_MConvexL1_SD_m_exc_iff
-- name    : MConvexL1.SD.m_exc_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:45:38.341004+00:00
-- url     : https://prove2.me/theorems/c1c81a55-1b5a-4343-bb10-d6f56b9a33a1
-- title:
--   §2.1, p. 4 — a function is M-convex if and only if it satisfies the exchange property (M-EXC)
-- statement:
--   Let $V$ be a finite set and $f : \mathbb Z^V \to \mathbb R \cup \{+\infty\}$. Call $f$ **M-convex** if it satisfies (M$^\natural$-EXC),
--   $$\forall x, y \in \operatorname{dom} f,\ \forall i \in \mathrm{supp}^+(x - y),\ \exists j \in \mathrm{supp}^-(x - y) \cup \{0\}:\ f(x) + f(y) \ge f(x - \chi_i + \chi_j) + f(y + \chi_i - \chi_j)$$
--   (with $\chi_0 = \mathbf 0$), and $\operatorname{dom} f$ lies in a hyperplane $\{x \mid x(V) = \theta\}$ for some $\theta \in \mathbb Z$. Then $f$ is M-convex if and only if it satisfies
--
--   $$(\text{M-EXC})\quad \forall x, y \in \operatorname{dom} f,\ \forall i \in \mathrm{supp}^+(x - y),\ \exists j \in \mathrm{supp}^-(x - y):\ f(x) + f(y) \ge f(x - \chi_i + \chi_j) + f(y + \chi_i - \chi_j).$$
--
--   The paper defines M-convexity through (M$^\natural$-EXC) and the hyperplane condition, while every argument of Appendix A.2 applies (M-EXC); this equivalence is the bridge between the two.
--
--   Differences from the source:
--   - generalization: N = {1, …, n} with n ≥ 2 (§2, p. 4) → an arbitrary finite type V with decidable equality (any cardinality, including 0 and 1); reason: taking V = Fin n with n ≥ 2 gives the paper's setting; for |V| ≤ 1 the hypotheses force dom f to be at most one point and the statement still holds
--   - encoding: f : ℤⁿ → ℝ ∪ {+∞} → f : (V → ℤ) → WithTop ℝ, dom f = {x | f x ≠ ⊤}; reason: Lean convention for ℝ ∪ {+∞}; same instances
--   - encoding: M-convex: (M♮-EXC) with ∃ j ∈ supp⁻(x − y) ∪ {0}, χ₀ = 0, and dom f in a hyperplane {x(N) = θ} (p. 4) → MConvex f := MNatExchangeAxiom f ∧ ∃ θ, ∀ x ∈ dom f, Σ x = θ, where MNatExchangeAxiom states f(x) + f(y) ≥ min(f(x − χ_i) + f(y + χ_i), min_{j ∈ supp⁻(x−y)} (f(x − χ_i + χ_j) + f(y + χ_i − χ_j))); reason: a minimum over a finite set in the linear order WithTop ℝ is attained, so the min form is the existential with j = 0 meaning χ₀ = 0
-- source:
--   Shioura, M-convex Function Minimization Under L1-Distance Constraint, arXiv:1809.03126v3, p. 4, §2.1, "It is known that a function f is M-convex if and only if it satisfies the following exchange property: (M-EXC)"

import Mathlib
import Definitions.Def_MConvexL1_SD_Basic
import Definitions.Def_DiscreteConvex_MConvexFunctions_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctions_ArgMin
open DiscreteConvex.MConvexFunctions DiscreteConvex.Algorithms

namespace MConvexL1.SD

theorem m_exc_iff {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ) :
    MConvex f ↔ MExchangeAxiom f := by sorry

end MConvexL1.SD
