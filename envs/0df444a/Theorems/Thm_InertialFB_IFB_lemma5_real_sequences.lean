-- Prove2me | Theorems.Thm_InertialFB_IFB_lemma5_real_sequences
-- name    : InertialFB.IFB.lemma5_real_sequences
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:51:03.876991+00:00
-- url     : https://prove2.me/theorems/7468e2e9-52c5-4347-8c18-03158a1cd607
-- title:
--   Lemma 5: a discrete second-order inequality forces $\theta \ge 0$
-- statement:
--   Let $(a_k)$, $(b_k)$ and $(\varepsilon_k)$ be real sequences with $(\varepsilon_k) \in \ell^1$, and let $\theta \in \mathbb R$. Suppose that for some $k_0 \ge 1$ and all $k \ge k_0$,
--   $$a_k - a_{k-1} \le \theta + \varepsilon_k, \qquad b_{k+1} - b_k \le a_k, \qquad b_k \ge 0.$$
--   Then $\theta \ge 0$.
--
--   In the paper this elementary lemma is applied with $a_k = F_k(q) - C$, $b_k = \alpha\|u_k - q\|^2$ and $\theta = b(\Theta(q) - E_\infty)$ to show that the IFB iterates minimize $\Theta$.
--
--   **Formalization Note** $(\varepsilon_k) \in \ell^1$ is `Summable ε`, which for real sequences is equivalent to absolute summability. The threshold is required to satisfy $k_0 \ge 1$ so that $a_{k-1}$ refers to an actual earlier term.
-- source:
--   Attouch, Peypouquet & Redont, A Dynamical Approach to an Inertial Forward-Backward Algorithm for Convex Minimization, authors' manuscript (Aug 2013) of SIAM J. Optim. (2014), DOI 10.1137/130910294, p. 9, Lemma 5

import Mathlib

namespace InertialFB.IFB

/-- **Lemma 5** (Attouch–Peypouquet–Redont, p. 9). Let `(a_k)`, `(b_k)`, `(ε_k)` be real
sequences with `(ε_k) ∈ ℓ¹`, and `θ ∈ ℝ`. If `a_k - a_{k-1} ≤ θ + ε_k`, `b_{k+1} - b_k ≤ a_k`
and `b_k ≥ 0` for all `k ≥ k₀` (with `k₀ ≥ 1`, so that `a_{k-1}` is defined), then `θ ≥ 0`. -/
theorem lemma5_real_sequences (a b ε : ℕ → ℝ) (θ : ℝ) (k₀ : ℕ) (hk₀ : 1 ≤ k₀)
    (hε : Summable ε)
    (h₁ : ∀ k : ℕ, k₀ ≤ k → a k - a (k - 1) ≤ θ + ε k)
    (h₂ : ∀ k : ℕ, k₀ ≤ k → b (k + 1) - b k ≤ a k)
    (h₃ : ∀ k : ℕ, k₀ ≤ k → 0 ≤ b k) :
    0 ≤ θ := by sorry

end InertialFB.IFB
