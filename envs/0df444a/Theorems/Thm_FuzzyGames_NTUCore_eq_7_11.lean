-- Prove2me | Theorems.Thm_FuzzyGames_NTUCore_eq_7_11
-- name    : FuzzyGames.NTUCore.eq_7_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:04:21.377873+00:00
-- url     : https://prove2.me/theorems/953aa725-d1bb-4786-abb1-da3d5b349328
-- title:
--   §7 (11) — the support function of πV(τ) is πv(τ, λ)
-- statement:
--   Let $\mathcal{C}$ be a family of nonempty coalitions of $N = \{1,\dots,n\}$ containing $N$ and every singleton, and let $V$ be a game without side payments on $\mathcal{C}$: for every $A \in \mathcal{C}$, $V(A)$ is a nonempty, closed, convex subset of $\mathbb{R}^A$ that is comprehensive and bounded above (§7 (1)). Its fuzzy extension is
--   $$\pi V(\tau) = \bigcup_{m \in \mathcal{C}(\tau)} \sum_{A \in \mathcal{C}} m(A)\, V(A),$$
--   where $\mathcal{C}(\tau)$ is the set of nonnegative weights $m$ on $\mathcal{C}$ with $\sum_{A \ni i} m(A) = \tau_i$ for every player $i$ (§6 (3)–(4), §7 (5)). Let $v(A,\lambda) = \sup_{c\in V(A)}\sum_{i\in A}\lambda^i c_i$. Then for every $\tau\in\mathbb{R}^n_+$ and every $\lambda\in\mathbb{R}^n_+$,
--   $$\sup_{c\in\pi V(\tau)}\sum_{i\in N}\lambda^i c_i = \pi v(\tau,\lambda) := \sup_{m\in\mathcal{C}(\tau)}\sum_{A\in\mathcal{C}} m(A)\,v(A,\lambda).$$
--
--   The identity transfers the equilibrium inequalities of the game $V$ to the fuzzy game $\pi V$ in the proof of Theorem 7.1.
--
--   **Formalization Note.** Both sides are computed in `EReal`. The paper uses $\pi v(\tau,\lambda)$ without defining it; we take it to be the extension §6 (2) applied to $A\mapsto v(A,\lambda)$. It is stated for $\lambda\ge 0$, where every $v(A,\lambda)$ is finite.
-- source:
--   Aubin, Cooperative Fuzzy Games, Math. Oper. Res. 6(1) (1981), §7 (11), p. 9

import Mathlib
import Definitions.Def_FuzzyGames_NTUCore_Basic

open Set Finset Pointwise

namespace FuzzyGames.NTUCore

/-- §7 (11), p. 9: for `τ ∈ ℝ^n_+` and `λ ∈ ℝ^n_+`, the support function of `πV(τ)` at `λ`
equals `πv(τ, λ) = sup_{m ∈ 𝒞(τ)} Σ_A m(A) v(A, λ)`. -/
theorem eq_7_11 {n : ℕ} (𝒞 : CoalFamily n) {V : Finset (Fin n) → Set (Fin n → ℝ)}
    (hV : IsNTUGame 𝒞 V) :
    ∀ τ ∈ orthant n, ∀ l : Fin n → ℝ, (∀ i, 0 ≤ l i) →
      supportFn (piV 𝒞 V τ) l = piv 𝒞 V τ l := by sorry

end FuzzyGames.NTUCore
