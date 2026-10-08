-- Prove2me | Theorems.Thm_FuzzyGames_NTUCore_piV_closed_convex
-- name    : FuzzyGames.NTUCore.piV_closed_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:04:18.716371+00:00
-- url     : https://prove2.me/theorems/243be049-795a-49a0-8d5f-7b3847b0368a
-- title:
--   §7, p. 9 — the sets πV(τ) are closed, convex, comprehensive and bounded above
-- statement:
--   Let $\mathcal{C}$ be a family of nonempty coalitions of $N = \{1,\dots,n\}$ containing $N$ and every singleton, and let $V$ be a game without side payments on $\mathcal{C}$: for every $A \in \mathcal{C}$, $V(A)$ is a nonempty, closed, convex subset of $\mathbb{R}^A$ that is comprehensive and bounded above (§7 (1)). Its fuzzy extension is
--   $$\pi V(\tau) = \bigcup_{m \in \mathcal{C}(\tau)} \sum_{A \in \mathcal{C}} m(A)\, V(A),$$
--   where $\mathcal{C}(\tau)$ is the set of nonnegative weights $m$ on $\mathcal{C}$ with $\sum_{A \ni i} m(A) = \tau_i$ for every player $i$ (§6 (3)–(4), §7 (5)). Then for every $\tau\in\mathbb{R}^n_+$ the set $\pi V(\tau)$ is
--
--   1. closed;
--   2. convex;
--   3. comprehensive: $\pi V(\tau) = \pi V(\tau) - \mathbb{R}^\tau_+$;
--   4. bounded above: $\pi V(\tau) \subseteq C - \mathbb{R}^\tau_+$ for some $C\in\mathbb{R}^\tau$;
--
--   and it is moreover a nonempty subset of $\mathbb{R}^\tau$.
--
--   Together with §7 (7)(i) this says that $\pi V$ is a fuzzy game without side payments in the sense of §3 (3), the input of Theorem 5.1.
--
--   **Formalization Note.** The paper's sentence lists the four properties 1–4. The last two (nonempty, contained in $\mathbb{R}^\tau$) are the remaining requirements of §3 (3)(i) that §7 uses when it applies Theorem 5.1 to $\pi V$; nonemptiness holds because every singleton belongs to $\mathcal{C}$.
-- source:
--   Aubin, Cooperative Fuzzy Games, Math. Oper. Res. 6(1) (1981), §7, p. 9, sentence after (5)

import Mathlib
import Definitions.Def_FuzzyGames_NTUCore_Basic

open Set Finset Pointwise

namespace FuzzyGames.NTUCore

/-- §7, p. 9, sentence after (5): for `τ ∈ ℝ^n_+`, `πV(τ)` is closed, convex, comprehensive and
bounded above; it is moreover a nonempty subset of `ℝ^τ`. -/
theorem piV_closed_convex {n : ℕ} (𝒞 : CoalFamily n) {V : Finset (Fin n) → Set (Fin n → ℝ)}
    (hV : IsNTUGame 𝒞 V) :
    ∀ τ ∈ orthant n,
      IsClosed (piV 𝒞 V τ) ∧ Convex ℝ (piV 𝒞 V τ) ∧
      piV 𝒞 V τ - RtauNonneg τ = piV 𝒞 V τ ∧
      (∃ C ∈ Rtau τ, piV 𝒞 V τ ⊆ {C} - RtauNonneg τ) ∧
      (piV 𝒞 V τ).Nonempty ∧ piV 𝒞 V τ ⊆ Rtau τ := by sorry

end FuzzyGames.NTUCore
