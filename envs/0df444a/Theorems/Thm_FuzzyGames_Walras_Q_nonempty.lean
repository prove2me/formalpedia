-- Prove2me | Theorems.Thm_FuzzyGames_Walras_Q_nonempty
-- name    : FuzzyGames.Walras.Q_nonempty
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:07:10.396985+00:00
-- url     : https://prove2.me/theorems/573cf016-7892-41b2-9e8b-664bc310599b
-- title:
--   Proof of Theorem 4.1 — the sets Q(i) = Y(i) − {x ≻ᵢ x̄ⁱ} are nonempty
-- statement:
--   Let an exchange economy satisfy the assumptions of §4 and let $\bar x \in X(N)$ be an allocation. For each consumer $i$ define
--   $$Q(i) = Y(i) - \{x^i \in \mathbb{R}^l_+ : x^i \succ_i \bar x^i\},$$
--   the Minkowski difference of the endowment set and the set of bundles consumer $i$ strictly prefers to $\bar x^i$. Then every $Q(i)$ is nonempty.
--
--   The paper attributes this to the insatiability assumption (together with the nonemptiness of $Y(i)$, which positive endowment gives). The sets $Q(i)$ are the ones separated from the origin in the proof of Theorem 4.1.
--
--   **Formalization Note.** $\bar x \in X(N)$ gives $\bar x^i \in \mathbb{R}^l_+$ for every $i$, which is where non-satiation applies.
-- source:
--   Aubin, Cooperative Fuzzy Games, Math. Oper. Res. 6(1) (1981), proof of Theorem 4.1, p. 6

import Mathlib
import Definitions.Def_FuzzyGames_Walras_Basic

namespace FuzzyGames.Walras

/-- Proof of Theorem 4.1 (Aubin 1981, p. 6): for an allocation `x̄ ∈ X(N)`, every set
`Q(i) = Y(i) − {x ∈ ℝ^l_+ | x ≻_i x̄^i}` is nonempty. -/
theorem Q_nonempty {n l : ℕ} (E : Economy n l) (hE : E.Assumptions)
    (xbar : Fin n → Fin l → ℝ) (hx : xbar ∈ E.X 1) (i : Fin n) :
    (E.Q xbar i).Nonempty := by sorry

end FuzzyGames.Walras
