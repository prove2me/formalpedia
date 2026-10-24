-- Prove2me | Theorems.Thm_MConvexL1_SD_lemma_A_3
-- name    : MConvexL1.SD.lemma_A_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:45:50.935765+00:00
-- url     : https://prove2.me/theorems/bd995ed3-84ff-4987-a5c5-3b109a168520
-- title:
--   Lemma A.3, Appendix A.2, p. 17 — from y with ‖y − x_c‖₁ < 2τ a strictly decreasing monotone sequence reaches the nearest point x• of M_τ
-- statement:
--   Throughout, $V$ is a finite ground set (the paper's $N = \{1,\dots,n\}$), vectors are integer vectors $x \in \mathbb Z^V$, $x(V) = \sum_{v} x(v)$, $\chi_i$ is the $i$-th unit vector, $\mathrm{supp}^+(z) = \{v \mid z(v) > 0\}$, $\mathrm{supp}^-(z) = \{v \mid z(v) < 0\}$ and $\|z\|_1 = \sum_v |z(v)|$. The function $f : \mathbb Z^V \to \mathbb R \cup \{+\infty\}$ is **M-convex** (in the paper's sense, p. 4), its effective domain $\operatorname{dom} f$ is **bounded**, and the **center** $x_c \in \mathbb Z^V$ satisfies $x_c(V) = \theta$ where $\operatorname{dom} f \subseteq \{x \mid x(V) = \theta\}$; the center need not lie in $\operatorname{dom} f$. For $k \in \mathbb Z_+$, $M_k$ is the set of optimal solutions of
--   $$(\mathrm{MML1}(k))\qquad \min\{ f(x) \mid x \in \operatorname{dom} f,\ \|x - x_c\|_1 \le 2k\},$$
--   and $\sigma, \tau \in \mathbb Z_+$ are defined by (4.1): $2\sigma = \min\{\|x - x_c\|_1 \mid x \in \operatorname{dom} f\}$ and $2\tau = \min\{\|x - x_c\|_1 \mid x \in \arg\min f\}$.
--
--   Let $y \in \operatorname{dom} f$ with $\|y - x_c\|_1 < 2\tau$, and let $x^\bullet \in M_\tau$ minimize $\|x^\bullet - y\|_1$ over $M_\tau$. Then there exists a **monotone sequence** $y_0, y_1, \dots, y_h \in \operatorname{dom} f$ with $h = \tfrac12 \|y - x^\bullet\|_1$ such that $y_0 = y$, $y_h = x^\bullet$ and
--
--   $$f(y_0) > f(y_1) > \cdots > f(y_h).$$
--
--   Here a sequence is monotone if $\|y_k - y_0\|_1 = 2k$ for $k = 0, \dots, h$ and each step is $y_{k+1} = y_k - \chi_i + \chi_j$ with $i \in \mathrm{supp}^+(y_k - y_h)$ and $j \in \mathrm{supp}^-(y_k - y_h)$. The lemma is the engine of Theorem 4.1 (i): walking from a point of $M_k$ towards the nearest minimizer strictly decreases $f$ and crosses the sphere $\|x - x_c\|_1 = 2(k+1)$.
--
--   Differences from the source:
--   - generalization: N = {1, …, n} with n ≥ 2 (§2, p. 4) → an arbitrary finite type V with decidable equality (any cardinality, including 0 and 1); reason: taking V = Fin n with n ≥ 2 gives the paper's setting; for |V| ≤ 1 the hypotheses force dom f to be at most one point and the statement still holds
--   - encoding: f : ℤⁿ → ℝ ∪ {+∞} → f : (V → ℤ) → WithTop ℝ, dom f = {x | f x ≠ ⊤}; reason: Lean convention for ℝ ∪ {+∞}; same instances
--   - encoding: ‖x − y‖₁ = Σ |x(i) − y(i)| → L1Dist x y = Σ_v |x v − y v| as a natural number; reason: the norm is a nonnegative integer; same values
--   - encoding: M-convex: (M♮-EXC) with ∃ j ∈ supp⁻(x − y) ∪ {0}, χ₀ = 0, and dom f in a hyperplane {x(N) = θ} (p. 4) → MConvex f := MNatExchangeAxiom f ∧ ∃ θ, ∀ x ∈ dom f, Σ x = θ, where MNatExchangeAxiom states f(x) + f(y) ≥ min(f(x − χ_i) + f(y + χ_i), min_{j ∈ supp⁻(x−y)} (f(x − χ_i + χ_j) + f(y + χ_i − χ_j))); reason: a minimum over a finite set in the linear order WithTop ℝ is attained, so the min form is the existential with j = 0 meaning χ₀ = 0
--   - encoding: dom f ⊆ {x | x(N) = θ} and x_c(N) = θ (p. 2), x_c possibly outside dom f (p. 7) → hxc : ∀ x ∈ dom f, Σ_v x v = Σ_v xc v, with θ eliminated; xc ∈ dom f is not assumed; reason: same condition with θ := x_c(N)
--   - encoding: τ = (1/2) min{‖x − x_c‖₁ | x ∈ arg min f} (4.1) → τ : ℕ with IsLeast {‖x − x_c‖₁ | x ∈ arg min f} (2τ); reason: same reason as for σ; arg min f ≠ ∅ follows from bounded dom f (p. 7)
--   - encoding: M_k = set of optimal solutions of (MML1(k)): minimize f(x) s.t. x(N) = θ, ‖x − x_c‖₁ ≤ 2k, x ∈ dom f (pp. 2, 8) → Mset f xc k = {x ∈ dom f | ‖x − x_c‖₁ ≤ 2k ∧ ∀ y ∈ dom f, ‖y − x_c‖₁ ≤ 2k → f x ≤ f y}; reason: the constraint x(N) = θ is implied by x ∈ dom f under hxc, so omitting it changes no instance
--   - encoding: a finite sequence y_0, …, y_h with h = (1/2)‖y − x•‖₁ → s : ℕ → V → ℤ and h : ℕ with 2h = ‖y − x•‖₁; entries beyond h are unconstrained; reason: y and x• lie in dom f, hence on one hyperplane, so ‖y − x•‖₁ is even
--   - reading: monotone: ‖y_k − y_0‖₁ = 2k for k ≤ h, which "can be rewritten" as y_{k+1} = y_k − χ_i + χ_j with i ∈ supp⁺(y_k − y_h), j ∈ supp⁻(y_k − y_h) (p. 17) → IsMonotoneSeq requires all y_k ∈ dom f and both printed forms; reason: the two forms are not equivalent as printed (the step form is the stronger one and is what the proof of Theorem 4.1 (i) uses); the conjunction is the stronger reading, never the weaker
-- source:
--   Shioura, M-convex Function Minimization Under L1-Distance Constraint, arXiv:1809.03126v3, Appendix A.2, p. 17, Lemma A.3 (with the definition of a monotone sequence, p. 17)

import Mathlib
import Definitions.Def_MConvexL1_SD_Basic
import Definitions.Def_DiscreteConvex_MConvexFunctions_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctions_ArgMin
open DiscreteConvex.MConvexFunctions DiscreteConvex.Algorithms

namespace MConvexL1.SD

theorem lemma_A_3 {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ)
    (hf : MConvex f) (hbdd : BddDom f) (xc : V → ℤ)
    (hxc : ∀ x ∈ DomZ f, ∑ v, x v = ∑ v, xc v)
    (τ : ℕ) (hτ : IsLeast {d | ∃ x ∈ ArgMin f, L1Dist x xc = d} (2 * τ))
    (y : V → ℤ) (hy : y ∈ DomZ f) (hyc : L1Dist y xc < 2 * τ)
    (xs : V → ℤ) (hxs : xs ∈ Mset f xc τ)
    (hxs_near : ∀ x' ∈ Mset f xc τ, L1Dist xs y ≤ L1Dist x' y) :
    ∃ (s : ℕ → V → ℤ) (h : ℕ), 2 * h = L1Dist y xs ∧ s 0 = y ∧ s h = xs ∧
      IsMonotoneSeq f s h ∧ ∀ k < h, f (s (k + 1)) < f (s k) := by sorry

end MConvexL1.SD
