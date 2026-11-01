-- Prove2me | Theorems.Thm_ManIAL_theorem_3_8_oracle_complexity
-- name    : ManIAL.theorem_3_8_oracle_complexity
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:14:49.66785+00:00
-- url     : https://prove2.me/theorems/b1c7c3d1-ce66-4384-aa6f-2f17d8bab696
-- title:
--   Theorem 3.8 — oracle complexity of ManIAL: $\tilde O(\epsilon^{-3})$ with Option I, $O(\epsilon^{-3})$ with Option II (corrected: $\sigma_k=2^{k/3}$ in (b))
-- statement:
--   Suppose Assumption 1 holds: $\mathcal M\subseteq\mathbb R^n$ is compact with a retraction $R$ satisfying (2.1) with $\alpha,\beta>0$; $f$ is differentiable with $\ell_{\nabla f}$-Lipschitz gradient; $h:\mathbb R^m\to\mathbb R$ is convex and $\ell_h$-Lipschitz; $\mathcal A$ is linear; $\varphi=f+h\circ\mathcal A$ is bounded below on $\mathcal M$. Fix $x^0\in\mathcal M$, $y^0\in\mathbb R^m$ and $\beta_0>0$, and use Algorithm 2 (RGD) as the subroutine of ManIAL (Algorithm 1). One first-order oracle call computes $\nabla f$, a prox of $h$ and a retraction.
--
--   **(a)** Let $b>1$, $\sigma_k=b^k$, $\epsilon_k=1/\sigma_k$, Option I. For every $G>0$ there is a constant $C$ such that for every $\epsilon\in(0,1]$ and every run of ManIAL with Option I whose stepsizes use $G$ and whose subproblems satisfy $\|\nabla\psi_k\|\le G$ on $\mathcal M$, some outer index $K$ has: $(x^{K+1},y^{K+1},\bar z^{K+1})$ is an $\epsilon$-KKT point pair and the oracle calls through iteration $K$ number at most
--
--   $$
--   C\,\epsilon^{-3}\big(1+\log(1/\epsilon)\big)=\tilde O(\epsilon^{-3}).
--   $$
--
--   Moreover, for every $b>1$ such runs exist for some $G>0$.
--
--   **(b)** Let $\sigma_k=2^{k/3}$, Option II. For every $G>0$ there is a constant $C$ such that for every $\epsilon\in(0,1]$ and every such run, some outer index $K$ has: $(x^{K+1},y^{K+1},\bar z^{K+1})$ is an $\epsilon$-KKT point pair reached within
--
--   $$
--   C\,\epsilon^{-3}=O(\epsilon^{-3})
--   $$
--
--   oracle calls. Moreover, such runs exist for some $G>0$.
--
--   Here $\bar z^{K+1}=z^K-\sigma_K(\mathcal Ax^{K+1}-y^{K+1})$ and the constant $C$ depends only on the problem data, $b$ and $G$, not on $\epsilon$ or the run. Part (b) removes the logarithmic factor of part (a).
--
--   **Formalization Note** A run of Option I stops RGD at the first iterate meeting (3.12); a run of Option II takes any argmin over $2^k+1$ RGD iterates. The oracle count of outer iterations $0,\dots,K$ is $\sum_{k\le K}(N_k+1)$, with $N_k$ the gradient evaluations of the subroutine and one prox for $y^{k+1}$.
--
--   Differences from the source:
--   - generalization: M a compact Riemannian submanifold embedded in ℝⁿ with a retraction R → M any compact subset of ℝⁿ, T_xM the span of its tangent cone, R any map with R_x(T_xM) ⊆ M and the bounds (2.1) for some α, β > 0; reason: §3 uses (M, R) only through these properties; Proposition 2.2 gives them for every retraction on a compact submanifold, so the paper's setting is a special case
--   - generalization: y⁰ = Ax⁰ (Algorithm 1, step 2) → y⁰ arbitrary; reason: the bound (3.31) only uses (3.13); y⁰ = Ax⁰ is the special case (then z^k ≡ 0)
--   - correction: (b) σ_k = 1/2^{k/3} → σ_k = 2^{k/3}; reason: counterexample: M = S¹, A = I, h = ℓh‖·‖, f ≡ 0, y⁰ = Ax⁰; then z^k ≡ 0 and ‖Ax^{k+1} − y^{k+1}‖ = min(1, ℓh/σ_k) ≥ min(1, ℓh) when σ_k ≤ 1, so no iterate is ϵ-KKT for ϵ < min(1, ℓh); Algorithm 1 requires increasing σ_k and the proof of Theorem 3.6 uses σ_k = 2^{k/3}
--   - reading: Õ(ϵ⁻³), O(ϵ⁻³) calls → ∃ C (depending only on the data, b and G, chosen before ϵ and the run) with ≤ Cϵ⁻³(1 + log(1/ϵ)) in (a) and ≤ Cϵ⁻³ in (b), for every ϵ ∈ (0, 1]; reason: the standard meaning; the single logarithmic factor is the one (3.41) produces; ϵ ≤ 1 is the asymptotic regime
--   - reading: finds an ϵ-KKT point after at most … calls → some outer index K with (x^{K+1}, y^{K+1}, z̄^{K+1}) ϵ-KKT and oracleCalls through K at most the bound; reason: Theorems 3.5 and 3.6 certify exactly this triple
--   - reading: Option I with Algorithm 2 as subroutine → RGD from x^k with stepsize 1/L_k, stopped at its first iterate with ‖grad ψ_k‖ ≤ ϵ_k; reason: Option I returns x^{k+1} satisfying (3.12); the proof counts the RGD iterations needed to reach it (Lemma 3.4's T_k needs ψ_{k,min}, which no oracle provides)
--   - reading: Option II: RGD returns x^{k+1} with 2^k iterations → x^{k+1} = u_t for any t ≤ 2^k minimizing ‖grad ψ_k(u_s)‖ over s ≤ 2^k; reason: Algorithm 2's output is an argmin; every tie-break is covered
--   - reading: number of calls to the first-order oracle (Definition 3.7) → Σ_{k≤K}(N_k + 1), N_k = t_k + 1 (Option I) or 2^k + 1 (Option II) gradient evaluations, plus one prox per outer iteration; reason: each RGD step evaluates one gradient and one retraction and step 5 one prox; this is at least the proof's count Σ T_k
--   - reading: G of Lemma 3.3 (enters L_k) → for every G > 0, every run using G whose ψ_k satisfy ‖∇ψ_k‖ ≤ G on M; plus clauses asserting such runs exist for some G > 0; reason: G enters the algorithm through the stepsize; the existence clauses exclude a vacuous statement
--   - reading: dual step size β₀ → β₀ > 0; reason: a step size; (3.31) needs β₀ ≥ 0
--   - encoding: dist(−z, ∂h(y)) ≤ ϵ → ∃ g ∈ ∂h(y), ‖z + g‖ ≤ ϵ; reason: ∂h(y) is nonempty and compact for real-valued convex h, so the distance is attained
--   - encoding: log in (3.13); division by ‖Ax^{k+1} − y^{k+1}‖ = 0 → Real.log; Lean's x/0 = 0 gives β_{k+1} = 0; reason: β_{k+1} only enters through β_{k+1}(Ax^{k+1} − y^{k+1}) = 0, so the iterates are the same; (3.31) holds for the natural log
--   - encoding: Assumption 1: h : ℝᵐ → (−∞,+∞] proper closed convex and ℓh-Lipschitz; f ℓ∇f-smooth; ℝⁿ, ℝᵐ → h : ℝᵐ → ℝ convex with |h y − h y'| ≤ ℓh‖y − y'‖; f differentiable with ‖∇f x − ∇f x'‖ ≤ ℓ∇f‖x − x'‖; ℓ∇f, ℓh ≥ 0; EuclideanSpace ℝ (Fin n), (Fin m); reason: a Lipschitz h is finite everywhere, hence proper and closed; ℓ∇f-smooth means Lipschitz gradient; Lipschitz constants are nonnegative
-- source:
--   Deng, Hu, Wu & Wen, Oracle complexities of augmented Lagrangian methods for nonsmooth manifold optimization, arXiv:2404.05121v2, Theorem 3.8, p.14

import Mathlib
import Definitions.Def_ManIAL_RetrBounds
import Definitions.Def_ManIAL_psi
import Definitions.Def_ManIAL_zbar
import Definitions.Def_ManIAL_IsEpsKKT
import Definitions.Def_ManIAL_IsRunOptionI
import Definitions.Def_ManIAL_IsRunOptionII
import Definitions.Def_ManIAL_oracleCalls

namespace ManIAL

/-- **Theorem 3.8** (Oracle complexity of ManIAL) (Deng–Hu–Wu–Wen, arXiv:2404.05121v2, p.14),
parts (a) and (b), with (b)'s penalty corrected to `σ_k = 2^{k/3}`. Suppose Assumption 1 holds
and Algorithm 2 (RGD) is the subroutine of ManIAL (Algorithm 1).

(a) For every `b > 1` and `G > 0` there is a constant `C` such that for every `ϵ ∈ (0, 1]` and
every run of ManIAL with Option I, `σ_k = b^k`, `ϵ_k = 1/σ_k` and the constant `G` (bounding
`‖∇ψ_k‖` on `M` for every `k`), some outer iterate `(x^{K+1}, y^{K+1}, z̄^{K+1})` is an ϵ-KKT point
pair reached within `Cϵ⁻³(1 + log(1/ϵ))` first-order oracle calls — that is `Õ(ϵ⁻³)`; and for
every `b > 1` such runs exist for some `G > 0`.

(b) The same with Option II, `σ_k = 2^{k/3}` and the bound `Cϵ⁻³` — that is `O(ϵ⁻³)`; and such
runs exist for some `G > 0`.

**Formalization Note.** `M` is any compact subset of `ℝⁿ` and `R` any map with the retraction
bounds (2.1) (`RetrBounds`, provided by Proposition 2.2 for every retraction on a compact
submanifold); `y⁰ = y₀` is arbitrary (the paper sets `y⁰ = Ax⁰`); `β₀ > 0`. The constant `C` is
chosen before `ϵ` and the run and depends only on the data. `G` enters the algorithm through
`L_k` and is the run's own bound on `‖∇ψ_k‖` over `M`. An oracle call is one evaluation of
`∇f`, one prox and one retraction (Definition 3.7); `oracleCalls N K` counts the subroutine's
gradient evaluations plus one prox per outer iteration `0, …, K`. -/
theorem theorem_3_8_oracle_complexity {n m : ℕ} (M : Set (EuclideanSpace ℝ (Fin n)))
    (hM : IsCompact M)
    (R : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hR : RetrBounds M R α β)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (ℓf : ℝ) (hℓf : 0 ≤ ℓf) (hf : Differentiable ℝ f)
    (hfL : ∀ x x', ‖gradient f x - gradient f x'‖ ≤ ℓf * ‖x - x'‖)
    (h : EuclideanSpace ℝ (Fin m) → ℝ) (ℓh : ℝ) (hℓh : 0 ≤ ℓh) (hh : ConvexOn ℝ Set.univ h)
    (hhL : ∀ y y', |h y - h y'| ≤ ℓh * ‖y - y'‖)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hφ : BddBelow ((fun x => f x + h (A x)) '' M))
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ M) (y₀ : EuclideanSpace ℝ (Fin m))
    (β₀ : ℝ) (hβ₀ : 0 < β₀) :
    -- (a) Option I, σ_k = b^k, ϵ_k = 1/σ_k: Õ(ϵ⁻³) oracle calls
    (∀ b : ℝ, 1 < b → ∀ G : ℝ, 0 < G → ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ (x : ℕ → EuclideanSpace ℝ (Fin n)) (y z : ℕ → EuclideanSpace ℝ (Fin m)) (N : ℕ → ℕ),
        IsRunOptionI M R f h A α β ℓf G b β₀ x₀ y₀ x y z N →
        (∀ k : ℕ, ∀ u ∈ M, ‖gradient (psi f h A (b ^ k) (z k)) u‖ ≤ G) →
        ∃ K : ℕ,
          IsEpsKKT M f h A ε (x (K + 1)) (y (K + 1))
            (zbar (b ^ K) (z K) A (x (K + 1)) (y (K + 1))) ∧
          (oracleCalls N K : ℝ) ≤ C * ε ^ (-3 : ℤ) * (1 + Real.log (1 / ε))) ∧
    -- (a) such runs exist
    (∀ b : ℝ, 1 < b → ∃ G : ℝ, 0 < G ∧
      ∃ (x : ℕ → EuclideanSpace ℝ (Fin n)) (y z : ℕ → EuclideanSpace ℝ (Fin m)) (N : ℕ → ℕ),
        IsRunOptionI M R f h A α β ℓf G b β₀ x₀ y₀ x y z N ∧
        ∀ k : ℕ, ∀ u ∈ M, ‖gradient (psi f h A (b ^ k) (z k)) u‖ ≤ G) ∧
    -- (b) Option II, σ_k = 2^{k/3}: O(ϵ⁻³) oracle calls
    (∀ G : ℝ, 0 < G → ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ (x : ℕ → EuclideanSpace ℝ (Fin n)) (y z : ℕ → EuclideanSpace ℝ (Fin m)) (N : ℕ → ℕ),
        IsRunOptionII M R f h A α β ℓf G β₀ x₀ y₀ x y z N →
        (∀ k : ℕ, ∀ u ∈ M, ‖gradient (psi f h A ((2 : ℝ) ^ ((k : ℝ) / 3)) (z k)) u‖ ≤ G) →
        ∃ K : ℕ,
          IsEpsKKT M f h A ε (x (K + 1)) (y (K + 1))
            (zbar ((2 : ℝ) ^ ((K : ℝ) / 3)) (z K) A (x (K + 1)) (y (K + 1))) ∧
          (oracleCalls N K : ℝ) ≤ C * ε ^ (-3 : ℤ)) ∧
    -- (b) such runs exist
    (∃ G : ℝ, 0 < G ∧
      ∃ (x : ℕ → EuclideanSpace ℝ (Fin n)) (y z : ℕ → EuclideanSpace ℝ (Fin m)) (N : ℕ → ℕ),
        IsRunOptionII M R f h A α β ℓf G β₀ x₀ y₀ x y z N ∧
        ∀ k : ℕ, ∀ u ∈ M, ‖gradient (psi f h A ((2 : ℝ) ^ ((k : ℝ) / 3)) (z k)) u‖ ≤ G) := by sorry

end ManIAL
