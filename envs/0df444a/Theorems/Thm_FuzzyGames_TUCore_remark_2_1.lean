-- Prove2me | Theorems.Thm_FuzzyGames_TUCore_remark_2_1
-- name    : FuzzyGames.TUCore.remark_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:07:31.317438+00:00
-- url     : https://prove2.me/theorems/9376ce8f-650c-4af1-becb-84ca4cb4da71
-- title:
--   Remark 2.1 — a positively homogeneous worth function is concave iff it is superadditive
-- statement:
--   Let $v$ be a fuzzy game with side payments: $v(0)=0$ and $v(t\tau)=t\,v(\tau)$ for all $t>0$ and $\tau\in\mathbb R^n_+$. Then $v$ is concave on $\mathbb R^n_+$ if and only if it is superadditive there:
--   $$v(\tau+\sigma)\ge v(\tau)+v(\sigma)\qquad\text{for all }\tau,\sigma\in\mathbb R^n_+.$$
--
--   Superadditivity says that merging two fuzzy coalitions never loses worth ("l'union fait la force"), so concavity, the hypothesis of Proposition 2.1, has this game-theoretic reading.
--
--   **Formalization Note** The standing assumptions of §2 (positive homogeneity and $v(0)=0$) are hypotheses. Concavity and superadditivity are both taken on the orthant $\mathbb R^n_+$, the domain of the extended worth function.
-- source:
--   Aubin, Cooperative Fuzzy Games, Math. Oper. Res. 6(1) (1981), Remark 2.1, p. 3

import Mathlib
import Definitions.Def_FuzzyGames_TUCore_Basic

namespace FuzzyGames.TUCore

theorem remark_2_1 {n : ℕ} (v : (Fin n → ℝ) → ℝ) (hv : IsFuzzyTUGame v) :
    ConcaveOn ℝ (Set.Ici (0 : Fin n → ℝ)) v ↔
      ∀ τ σ : Fin n → ℝ, 0 ≤ τ → 0 ≤ σ → v (τ + σ) ≥ v τ + v σ := by sorry

end FuzzyGames.TUCore
