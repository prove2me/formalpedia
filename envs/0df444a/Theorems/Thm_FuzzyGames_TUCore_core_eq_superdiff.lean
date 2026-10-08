-- Prove2me | Theorems.Thm_FuzzyGames_TUCore_core_eq_superdiff
-- name    : FuzzyGames.TUCore.core_eq_superdiff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:07:23.052246+00:00
-- url     : https://prove2.me/theorems/4b7c3eba-8b2f-43b2-957d-32a512b70edd
-- title:
--   §2 (4) — the core of a fuzzy game with side payments is the superdifferential $\partial v(\tau^N)$
-- statement:
--   Let $v$ be a fuzzy game with side payments: $v(0)=0$ and $v(t\tau)=t\,v(\tau)$ for all $t>0$ and $\tau\in\mathbb R^n_+$. For $c\in\mathbb R^n$ the following are equivalent:
--
--   1. $\sum_{i\in N}c_i=v(\tau^N)$ and $\sum_{i\in N}\tau_ic_i\ge v(\tau)$ for every fuzzy coalition $\tau\in[0,1]^n$;
--   2. $c\in\partial v(\tau^N)$, i.e. $v(\tau^N)-v(\sigma)\ge\sum_{i\in N}c_i(1-\sigma_i)$ for every $\sigma\in\mathbb R^n_+$.
--
--   In other words,
--   $$\operatorname{core}(v)=\partial v(\tau^N).$$
--
--   This identification of the fuzzy core with a superdifferential is what lets convex analysis describe the core.
--
--   **Formalization Note** Positive homogeneity and $v(0)=0$ are the standing assumptions of §2 ("We assume in this section that"), so they are hypotheses here. The superdifferential is taken with $\sigma$ ranging over $\mathbb R^n_+$, the domain of the extended $v$; the paper leaves that range implicit.
-- source:
--   Aubin, Cooperative Fuzzy Games, Math. Oper. Res. 6(1) (1981), §2, (4)–(5), p. 3

import Mathlib
import Definitions.Def_FuzzyGames_TUCore_Basic

namespace FuzzyGames.TUCore

theorem core_eq_superdiff {n : ℕ} (v : (Fin n → ℝ) → ℝ) (hv : IsFuzzyTUGame v) :
    fuzzyCore v = superdiff v (FuzzyGames.NTUCore.coal Finset.univ) := by sorry

end FuzzyGames.TUCore
