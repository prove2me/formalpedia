-- Prove2me | Theorems.Thm_FuzzyGames_NTUCore_support_concave
-- name    : FuzzyGames.NTUCore.support_concave
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:03:34.424531+00:00
-- url     : https://prove2.me/theorems/449e317d-f081-48cd-9100-0e4c280f0a2b
-- title:
--   §3, proof of Theorem 3.1(b) — superadditivity makes τ ↦ v(τ, λ) concave on ℝ^n_+
-- statement:
--   Let $V$ be a fuzzy game without side payments: for every $\tau \in \mathbb{R}^n_+$, $V(\tau)$ is a nonempty, closed, convex subset of $\mathbb{R}^\tau$, comprehensive and bounded above, and $V(t\tau) = tV(\tau)$ for $t > 0$ (§3 (3)). Assume $V$ is superadditive: $V(\tau)+V(\sigma)\subseteq V(\tau+\sigma)$ for all $\tau,\sigma\in\mathbb{R}^n_+$. Fix $\lambda \in \mathbb{R}^n_+$. Then the support function $v(\tau,\lambda) = \sup_{c\in V(\tau)} \sum_i \lambda_i c_i$ is finite for every $\tau \in \mathbb{R}^n_+$, and
--   $$\tau \longmapsto v(\tau,\lambda)\quad\text{is concave on } \mathbb{R}^n_+.$$
--
--   Concavity in $\tau$ is the hypothesis of the minisup theorem in the proof of Theorem 3.1(b).
--
--   **Formalization Note.** The support function is `EReal`-valued; the statement first asserts that it is finite on the orthant (the paper notes on p. 4 that $v(\tau,\lambda)$ is finite iff $\lambda \in \mathbb{R}^\tau_+$), and then that its real value is concave on $\mathbb{R}^n_+$.
-- source:
--   Aubin, Cooperative Fuzzy Games, Math. Oper. Res. 6(1) (1981), §3, proof of Theorem 3.1(b), p. 5

import Mathlib
import Definitions.Def_FuzzyGames_NTUCore_Basic

open Set Finset Pointwise

namespace FuzzyGames.NTUCore

/-- §3, proof of Theorem 3.1(b) (p. 5): under superadditivity (9), for every `λ ∈ ℝ^n_+` the
support function `τ ↦ v(τ, λ)` is finite and concave on `ℝ^n_+`. -/
theorem support_concave {n : ℕ} {V : (Fin n → ℝ) → Set (Fin n → ℝ)} (hV : IsNTUFuzzyGame V)
    (hsup : Superadditive V) {l : Fin n → ℝ} (hl : ∀ i, 0 ≤ l i) :
    (∀ τ ∈ orthant n, ∃ r : ℝ, supportFn (V τ) l = (r : EReal)) ∧
      ConcaveOn ℝ (orthant n) (fun τ => (supportFn (V τ) l).toReal) := by sorry

end FuzzyGames.NTUCore
