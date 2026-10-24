-- Prove2me | Theorems.Thm_MConvexL1_SD_theorem_4_2
-- name    : MConvexL1.SD.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:46:00.344058+00:00
-- url     : https://prove2.me/theorems/167f39b2-cfd4-457e-96f7-7caae15a153f
-- title:
--   Theorem 4.2, p. 8 — every run of SteepestDescentMML1 from x_σ ∈ M_σ has x_k ∈ M_k for all k ≤ γ, so x_γ is optimal for (MML1)
-- statement:
--   Throughout, $V$ is a finite ground set (the paper's $N = \{1,\dots,n\}$), vectors are integer vectors $x \in \mathbb Z^V$, $x(V) = \sum_{v} x(v)$, $\chi_i$ is the $i$-th unit vector, $\mathrm{supp}^+(z) = \{v \mid z(v) > 0\}$, $\mathrm{supp}^-(z) = \{v \mid z(v) < 0\}$ and $\|z\|_1 = \sum_v |z(v)|$. The function $f : \mathbb Z^V \to \mathbb R \cup \{+\infty\}$ is **M-convex** (in the paper's sense, p. 4), its effective domain $\operatorname{dom} f$ is **bounded**, and the **center** $x_c \in \mathbb Z^V$ satisfies $x_c(V) = \theta$ where $\operatorname{dom} f \subseteq \{x \mid x(V) = \theta\}$; the center need not lie in $\operatorname{dom} f$. For $k \in \mathbb Z_+$, $M_k$ is the set of optimal solutions of
--   $$(\mathrm{MML1}(k))\qquad \min\{ f(x) \mid x \in \operatorname{dom} f,\ \|x - x_c\|_1 \le 2k\},$$
--   and $\sigma, \tau \in \mathbb Z_+$ are defined by (4.1): $2\sigma = \min\{\|x - x_c\|_1 \mid x \in \operatorname{dom} f\}$ and $2\tau = \min\{\|x - x_c\|_1 \mid x \in \arg\min f\}$.
--
--   **Algorithm SteepestDescentMML1** (p. 8), for an integer $\gamma \ge \sigma$:
--   Step 0: choose $x_\sigma \in M_\sigma$ and set $k := \sigma + 1$. Step 1: if $k - 1 = \gamma$, output $x_{k-1}$ and stop. Step 2: find $i_k, j_k \in V$ minimizing $f(x_{k-1} + \chi_{i_k} - \chi_{j_k})$ over all pairs. Step 3: set $x_k := x_{k-1} + \chi_{i_k} - \chi_{j_k}$, $k := k + 1$, and go to Step 1.
--
--   **Theorem.** Every run of the algorithm, with any choice in Step 0 and any tie-breaking in Step 2, outputs after $\gamma - \sigma$ iterations an optimal solution of
--   $$(\mathrm{MML1})\qquad \min\{ f(x) \mid x(V) = \theta,\ \|x - x_c\|_1 \le 2\gamma,\ x \in \operatorname{dom} f\};$$
--   moreover every iterate satisfies $x_k \in M_k$ for $\sigma \le k \le \gamma$.
--
--   This is the paper's pseudo-polynomial algorithm for M-convex minimization under an $\ell_1$-distance constraint: greedy single exchanges started at the nearest feasible point are optimal at every radius simultaneously. In the bike-sharing application (§3, §6) the radius is the number of docks moved.
--
--   Differences from the source:
--   - generalization: N = {1, …, n} with n ≥ 2 (§2, p. 4) → an arbitrary finite type V with decidable equality (any cardinality, including 0 and 1); reason: taking V = Fin n with n ≥ 2 gives the paper's setting; for |V| ≤ 1 the hypotheses force dom f to be at most one point and the statement still holds
--   - generalization: the standing assumption τ > γ of §4 (p. 8: "Hence, we assume τ > γ in the following") → no assumption relating τ and γ; τ does not appear; reason: for γ < τ it is the printed theorem; for k ≥ τ one has M_k = {x ∈ arg min f | ‖x − x_c‖₁ ≤ 2k} (p. 8), and the paper itself applies the theorem with γ = τ (Corollary A.5, p. 19)
--   - encoding: f : ℤⁿ → ℝ ∪ {+∞} → f : (V → ℤ) → WithTop ℝ, dom f = {x | f x ≠ ⊤}; reason: Lean convention for ℝ ∪ {+∞}; same instances
--   - encoding: ‖x − y‖₁ = Σ |x(i) − y(i)| → L1Dist x y = Σ_v |x v − y v| as a natural number; reason: the norm is a nonnegative integer; same values
--   - encoding: M-convex: (M♮-EXC) with ∃ j ∈ supp⁻(x − y) ∪ {0}, χ₀ = 0, and dom f in a hyperplane {x(N) = θ} (p. 4) → MConvex f := MNatExchangeAxiom f ∧ ∃ θ, ∀ x ∈ dom f, Σ x = θ, where MNatExchangeAxiom states f(x) + f(y) ≥ min(f(x − χ_i) + f(y + χ_i), min_{j ∈ supp⁻(x−y)} (f(x − χ_i + χ_j) + f(y + χ_i − χ_j))); reason: a minimum over a finite set in the linear order WithTop ℝ is attained, so the min form is the existential with j = 0 meaning χ₀ = 0
--   - encoding: dom f ⊆ {x | x(N) = θ} and x_c(N) = θ (p. 2), x_c possibly outside dom f (p. 7) → hxc : ∀ x ∈ dom f, Σ_v x v = Σ_v xc v, with θ eliminated; xc ∈ dom f is not assumed; reason: same condition with θ := x_c(N)
--   - encoding: σ = (1/2) min{‖x − x_c‖₁ | x ∈ dom f} (4.1) → σ : ℕ with IsLeast {‖x − x_c‖₁ | x ∈ dom f} (2σ); reason: under hxc every such distance is even, so this is the paper's half-minimum; it also records dom f ≠ ∅, which the paper's min presupposes
--   - encoding: M_k = set of optimal solutions of (MML1(k)): minimize f(x) s.t. x(N) = θ, ‖x − x_c‖₁ ≤ 2k, x ∈ dom f (pp. 2, 8) → Mset f xc k = {x ∈ dom f | ‖x − x_c‖₁ ≤ 2k ∧ ∀ y ∈ dom f, ‖y − x_c‖₁ ≤ 2k → f x ≤ f y}; reason: the constraint x(N) = θ is implied by x ∈ dom f under hxc, so omitting it changes no instance
--   - encoding: the algorithm stops after γ − σ iterations, which presupposes γ ≥ σ → hypothesis σ ≤ γ; reason: for γ < σ the problem (MML1) is infeasible and Step 1 never fires; the hypothesis only excludes this undefined case
--   - encoding: Algorithm SteepestDescentMML1, Steps 0–3 (p. 8), with any choice in Step 0 and any tie-break in Step 2 → IsSDRun f xc σ γ x: x σ ∈ M_σ and, for σ < k ≤ γ, x k = x (k−1) + χ_i − χ_j for a pair (i, j) ∈ V × V minimizing f(x (k−1) + χ_i − χ_j) over all pairs; reason: the run is the sequence of iterates; quantifying over every such sequence covers every execution
--   - encoding: "outputs an optimal solution of (MML1)" → x γ ∈ M_γ; reason: M_γ is exactly the set of optimal solutions of (MML1) with radius 2γ
-- source:
--   Shioura, M-convex Function Minimization Under L1-Distance Constraint, arXiv:1809.03126v3, p. 8, Theorem 4.2 (algorithm SteepestDescentMML1, p. 8)

import Mathlib
import Definitions.Def_MConvexL1_SD_Basic
import Definitions.Def_DiscreteConvex_MConvexFunctions_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctions_ArgMin
open DiscreteConvex.MConvexFunctions DiscreteConvex.Algorithms

namespace MConvexL1.SD

theorem theorem_4_2 {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ)
    (hf : MConvex f) (hbdd : BddDom f) (xc : V → ℤ)
    (hxc : ∀ x ∈ DomZ f, ∑ v, x v = ∑ v, xc v)
    (σ γ : ℕ) (hσ : IsLeast {d | ∃ x ∈ DomZ f, L1Dist x xc = d} (2 * σ)) (hγ : σ ≤ γ)
    (x : ℕ → V → ℤ) (hrun : IsSDRun f xc σ γ x) :
    (∀ k, σ ≤ k → k ≤ γ → x k ∈ Mset f xc k) ∧ x γ ∈ Mset f xc γ := by sorry

end MConvexL1.SD
