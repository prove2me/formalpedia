-- Prove2me | Theorems.Thm_MConvexL1_SD_theorem_4_1_i
-- name    : MConvexL1.SD.theorem_4_1_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:45:52.594452+00:00
-- url     : https://prove2.me/theorems/29623179-6134-47b9-87a8-1f42c34c1c60
-- title:
--   Theorem 4.1 (i), p. 8, part (i) of 3 ((ii), (iii) are theorem_4_1_ii, theorem_4_1_iii) — μ_σ > ⋯ > μ_τ and M_k lies on the sphere ‖x − x_c‖₁ = 2k
-- statement:
--   Throughout, $V$ is a finite ground set (the paper's $N = \{1,\dots,n\}$), vectors are integer vectors $x \in \mathbb Z^V$, $x(V) = \sum_{v} x(v)$, $\chi_i$ is the $i$-th unit vector, $\mathrm{supp}^+(z) = \{v \mid z(v) > 0\}$, $\mathrm{supp}^-(z) = \{v \mid z(v) < 0\}$ and $\|z\|_1 = \sum_v |z(v)|$. The function $f : \mathbb Z^V \to \mathbb R \cup \{+\infty\}$ is **M-convex** (in the paper's sense, p. 4), its effective domain $\operatorname{dom} f$ is **bounded**, and the **center** $x_c \in \mathbb Z^V$ satisfies $x_c(V) = \theta$ where $\operatorname{dom} f \subseteq \{x \mid x(V) = \theta\}$; the center need not lie in $\operatorname{dom} f$. For $k \in \mathbb Z_+$, $M_k$ is the set of optimal solutions of
--   $$(\mathrm{MML1}(k))\qquad \min\{ f(x) \mid x \in \operatorname{dom} f,\ \|x - x_c\|_1 \le 2k\},$$
--   and $\sigma, \tau \in \mathbb Z_+$ are defined by (4.1): $2\sigma = \min\{\|x - x_c\|_1 \mid x \in \operatorname{dom} f\}$ and $2\tau = \min\{\|x - x_c\|_1 \mid x \in \arg\min f\}$.
--
--   Then for every integer $k \in [\sigma, \tau]$ the problem (MML1($k$)) has an optimal solution, its optimal value $\mu_k$ satisfies
--
--   $$\mu_\sigma > \mu_{\sigma+1} > \cdots > \mu_\tau,$$
--
--   and every optimal solution lies on the sphere: $M_k \subseteq \{x \in \mathbb Z^V \mid \|x - x_c\|_1 = 2k\}$ for $k \in [\sigma, \tau]$.
--
--   Part (i) of Theorem 4.1; parts (ii) and (iii) are separate items. It says that until the radius reaches the distance of the nearest minimizer, enlarging the radius strictly improves the optimum and the constraint is tight.
--
--   Differences from the source:
--   - generalization: N = {1, …, n} with n ≥ 2 (§2, p. 4) → an arbitrary finite type V with decidable equality (any cardinality, including 0 and 1); reason: taking V = Fin n with n ≥ 2 gives the paper's setting; for |V| ≤ 1 the hypotheses force dom f to be at most one point and the statement still holds
--   - encoding: f : ℤⁿ → ℝ ∪ {+∞} → f : (V → ℤ) → WithTop ℝ, dom f = {x | f x ≠ ⊤}; reason: Lean convention for ℝ ∪ {+∞}; same instances
--   - encoding: ‖x − y‖₁ = Σ |x(i) − y(i)| → L1Dist x y = Σ_v |x v − y v| as a natural number; reason: the norm is a nonnegative integer; same values
--   - encoding: M-convex: (M♮-EXC) with ∃ j ∈ supp⁻(x − y) ∪ {0}, χ₀ = 0, and dom f in a hyperplane {x(N) = θ} (p. 4) → MConvex f := MNatExchangeAxiom f ∧ ∃ θ, ∀ x ∈ dom f, Σ x = θ, where MNatExchangeAxiom states f(x) + f(y) ≥ min(f(x − χ_i) + f(y + χ_i), min_{j ∈ supp⁻(x−y)} (f(x − χ_i + χ_j) + f(y + χ_i − χ_j))); reason: a minimum over a finite set in the linear order WithTop ℝ is attained, so the min form is the existential with j = 0 meaning χ₀ = 0
--   - encoding: dom f ⊆ {x | x(N) = θ} and x_c(N) = θ (p. 2), x_c possibly outside dom f (p. 7) → hxc : ∀ x ∈ dom f, Σ_v x v = Σ_v xc v, with θ eliminated; xc ∈ dom f is not assumed; reason: same condition with θ := x_c(N)
--   - encoding: σ = (1/2) min{‖x − x_c‖₁ | x ∈ dom f} (4.1) → σ : ℕ with IsLeast {‖x − x_c‖₁ | x ∈ dom f} (2σ); reason: under hxc every such distance is even, so this is the paper's half-minimum; it also records dom f ≠ ∅, which the paper's min presupposes
--   - encoding: τ = (1/2) min{‖x − x_c‖₁ | x ∈ arg min f} (4.1) → τ : ℕ with IsLeast {‖x − x_c‖₁ | x ∈ arg min f} (2τ); reason: same reason as for σ; arg min f ≠ ∅ follows from bounded dom f (p. 7)
--   - encoding: M_k = set of optimal solutions of (MML1(k)): minimize f(x) s.t. x(N) = θ, ‖x − x_c‖₁ ≤ 2k, x ∈ dom f (pp. 2, 8) → Mset f xc k = {x ∈ dom f | ‖x − x_c‖₁ ≤ 2k ∧ ∀ y ∈ dom f, ‖y − x_c‖₁ ≤ 2k → f x ≤ f y}; reason: the constraint x(N) = θ is implied by x ∈ dom f under hxc, so omitting it changes no instance
--   - encoding: μ_k ∈ ℝ, the optimal value of (MML1(k)), and the chain μ_σ > μ_{σ+1} > ⋯ > μ_τ → M_k is nonempty for σ ≤ k ≤ τ, and f y' < f y for all y ∈ M_k, y' ∈ M_{k+1}, σ ≤ k < τ; reason: μ_k is the common value of f on M_k; nonemptiness is what makes μ_k ∈ ℝ, and without it the comparison would hold vacuously
-- source:
--   Shioura, M-convex Function Minimization Under L1-Distance Constraint, arXiv:1809.03126v3, p. 8, Theorem 4.1 (i) (proof Appendix A.2, p. 17)

import Mathlib
import Definitions.Def_MConvexL1_SD_Basic
import Definitions.Def_DiscreteConvex_MConvexFunctions_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctions_ArgMin
open DiscreteConvex.MConvexFunctions DiscreteConvex.Algorithms

namespace MConvexL1.SD

theorem theorem_4_1_i {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ)
    (hf : MConvex f) (hbdd : BddDom f) (xc : V → ℤ)
    (hxc : ∀ x ∈ DomZ f, ∑ v, x v = ∑ v, xc v)
    (σ τ : ℕ) (hσ : IsLeast {d | ∃ x ∈ DomZ f, L1Dist x xc = d} (2 * σ))
    (hτ : IsLeast {d | ∃ x ∈ ArgMin f, L1Dist x xc = d} (2 * τ)) :
    (∀ k, σ ≤ k → k ≤ τ → (Mset f xc k).Nonempty) ∧
    (∀ k, σ ≤ k → k < τ → ∀ y ∈ Mset f xc k, ∀ y' ∈ Mset f xc (k + 1), f y' < f y) ∧
    (∀ k, σ ≤ k → k ≤ τ → ∀ x ∈ Mset f xc k, L1Dist x xc = 2 * k) := by sorry

end MConvexL1.SD
