-- Prove2me | Theorems.Thm_FuzzyGames_NTUCore_eq_7_7
-- name    : FuzzyGames.NTUCore.eq_7_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:04:06.487073+00:00
-- url     : https://prove2.me/theorems/6c00f6d0-f693-4ce1-92de-29c972e7a4b5
-- title:
--   §7 (7) — πV is positively homogeneous and superadditive
-- statement:
--   Let $\mathcal{C}$ be a family of nonempty coalitions of $N = \{1,\dots,n\}$ containing $N$ and every singleton, and let $V$ be a game without side payments on $\mathcal{C}$: for every $A \in \mathcal{C}$, $V(A)$ is a nonempty, closed, convex subset of $\mathbb{R}^A$ that is comprehensive and bounded above (§7 (1)). Its fuzzy extension is
--   $$\pi V(\tau) = \bigcup_{m \in \mathcal{C}(\tau)} \sum_{A \in \mathcal{C}} m(A)\, V(A),$$
--   where $\mathcal{C}(\tau)$ is the set of nonnegative weights $m$ on $\mathcal{C}$ with $\sum_{A \ni i} m(A) = \tau_i$ for every player $i$ (§6 (3)–(4), §7 (5)). Then
--
--   1. $\pi V(t\tau) = t\,\pi V(\tau)$ for every $t > 0$ and $\tau\in\mathbb{R}^n_+$;
--   2. $\pi V(\tau+\sigma)\supseteq \pi V(\tau)+\pi V(\sigma)$ for all $\tau,\sigma\in\mathbb{R}^n_+$.
--
--   These are assumption (iii) of §3 (3) and assumption (1) of Theorem 5.1 for the fuzzy game $\pi V$.
--
--   **Formalization Note.** The paper writes $\forall\lambda > 0$ for the scaling factor; it is $t$ here, and $\tau$ ranges over the orthant, the domain on which fuzzy games are defined.
-- source:
--   Aubin, Cooperative Fuzzy Games, Math. Oper. Res. 6(1) (1981), §7 (7), p. 9

import Mathlib
import Definitions.Def_FuzzyGames_NTUCore_Basic

open Set Finset Pointwise

namespace FuzzyGames.NTUCore

/-- §7 (7), p. 9: `πV` is positively homogeneous and superadditive on `ℝ^n_+`. -/
theorem eq_7_7 {n : ℕ} (𝒞 : CoalFamily n) {V : Finset (Fin n) → Set (Fin n → ℝ)}
    (hV : IsNTUGame 𝒞 V) :
    (∀ t : ℝ, 0 < t → ∀ τ ∈ orthant n, piV 𝒞 V (t • τ) = t • piV 𝒞 V τ) ∧
      (∀ τ ∈ orthant n, ∀ σ ∈ orthant n, piV 𝒞 V τ + piV 𝒞 V σ ⊆ piV 𝒞 V (τ + σ)) := by sorry

end FuzzyGames.NTUCore
