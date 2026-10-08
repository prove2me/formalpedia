-- Prove2me | Theorems.Thm_FuzzyGames_TUCore_proposition_2_1
-- name    : FuzzyGames.TUCore.proposition_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:07:16.631989+00:00
-- url     : https://prove2.me/theorems/d1a03878-162a-4594-816a-7a9a94763380
-- title:
--   Proposition 2.1 — a concave fuzzy game has a convex, compact, nonempty core, equal to $\{Dv(\tau^N)\}$ when $v$ is differentiable at $\tau^N$
-- statement:
--   Let $v$ be a fuzzy game with side payments ($v(0)=0$, $v(t\tau)=t\,v(\tau)$ for $t>0$, $\tau\in\mathbb R^n_+$) that is concave on $\mathbb R^n_+$. Then:
--
--   1. the core of $v$, the set of $c\in\mathbb R^n$ with $\sum_{i\in N}c_i=v(\tau^N)$ and $\sum_{i\in N}\tau_ic_i\ge v(\tau)$ for all $\tau\in[0,1]^n$, is convex, compact and nonempty;
--   2. if moreover $v$ is differentiable at $\tau^N=(1,\dots,1)$, then
--   $$\operatorname{core}(v)=\{Dv(\tau^N)\},$$
--   where $Dv(\tau^N)=\big(\partial v/\partial\tau_i(\tau^N)\big)_{i\in N}$ is the gradient.
--
--   This is the existence result behind the paper's construction: any game whose worth function can be extended to a concave positively homogeneous function of fuzzy coalitions has a nonempty core.
--
--   **Formalization Note** The proposition's sentence assumes only concavity; positive homogeneity and $v(0)=0$ are the standing assumptions of §2 and are hypotheses here. Concavity is on the orthant $\mathbb R^n_+$. Since $\tau^N$ is an interior point of $\mathbb R^n_+$, differentiability of $v$ at $\tau^N$ (as a function on $\mathbb R^n$) depends only on values on the orthant. The gradient is the vector of the Fréchet derivative's values on the standard basis vectors.
-- source:
--   Aubin, Cooperative Fuzzy Games, Math. Oper. Res. 6(1) (1981), Proposition 2.1, p. 3

import Mathlib
import Definitions.Def_FuzzyGames_TUCore_Basic

namespace FuzzyGames.TUCore

theorem proposition_2_1 {n : ℕ} (v : (Fin n → ℝ) → ℝ) (hv : IsFuzzyTUGame v)
    (hconc : ConcaveOn ℝ (Set.Ici (0 : Fin n → ℝ)) v) :
    (Convex ℝ (fuzzyCore v) ∧ IsCompact (fuzzyCore v) ∧ (fuzzyCore v).Nonempty) ∧
      (DifferentiableAt ℝ v (FuzzyGames.NTUCore.coal Finset.univ) →
        fuzzyCore v = {grad v (FuzzyGames.NTUCore.coal Finset.univ)}) := by sorry

end FuzzyGames.TUCore
