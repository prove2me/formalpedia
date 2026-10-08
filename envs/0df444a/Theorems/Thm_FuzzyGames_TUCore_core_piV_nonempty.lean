-- Prove2me | Theorems.Thm_FuzzyGames_TUCore_core_piV_nonempty
-- name    : FuzzyGames.TUCore.core_piV_nonempty
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:07:38.994749+00:00
-- url     : https://prove2.me/theorems/f174faf1-1a00-46b3-9469-fd52f14c4305
-- title:
--   §6, after (6) — the core of the fuzzy game $\pi v$ is nonempty, convex and compact
-- statement:
--   Let $\mathscr C$ be a family of nonempty coalitions containing $N$ and every singleton, and let $v:\mathscr C\to\mathbb R$ be any game with side payments, balanced or not. The core of the fuzzy game $\pi v$,
--   $$\Big\{c\in\mathbb R^n:\ \sum_{i\in N}c_i=\pi v(\tau^N),\ \ \sum_{i\in N}\tau_ic_i\ge\pi v(\tau)\ \text{ for all }\tau\in[0,1]^n\Big\},$$
--   is nonempty, convex and compact.
--
--   Combined with Proposition 6.1, this is the step from the fuzzy extension back to the usual game: when $v$ is balanced the two cores coincide.
--
--   **Formalization Note** $\pi v$ is the real-valued supremum of the definition file, used only on $[0,1]^n$ here.
-- source:
--   Aubin, Cooperative Fuzzy Games, Math. Oper. Res. 6(1) (1981), §6, p. 8, sentence after (6)

import Mathlib
import Definitions.Def_FuzzyGames_TUCore_Basic

namespace FuzzyGames.TUCore

theorem core_piV_nonempty {n : ℕ} (𝒞 : FuzzyGames.NTUCore.CoalFamily n) (v : Finset (Fin n) → ℝ) :
    (fuzzyCore (piV 𝒞 v)).Nonempty ∧ Convex ℝ (fuzzyCore (piV 𝒞 v)) ∧
      IsCompact (fuzzyCore (piV 𝒞 v)) := by sorry

end FuzzyGames.TUCore
