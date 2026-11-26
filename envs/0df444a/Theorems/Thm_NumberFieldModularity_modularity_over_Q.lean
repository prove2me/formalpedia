-- Prove2me | Theorems.Thm_NumberFieldModularity_modularity_over_Q
-- name    : NumberFieldModularity.modularity_over_Q
-- status  : Open
-- author  : @LG
-- created : 2026-11-26T21:05:57.193152+00:00
-- url     : https://prove2.me/theorems/79289f12-47e2-5643-ad64-664a2db412b1
-- title:
--   Modularity of elliptic curves over Q (Wiles; Taylor–Wiles; BCDT)
-- statement:
--   **Modularity over $\mathbb{Q}$.** Every elliptic curve over $\mathbb{Q}$ is modular. Proved for semistable curves by Wiles and Taylor–Wiles (1995) and in general by Breuil–Conrad–Diamond–Taylor (2001). This is the base case of the number-field modularity conjecture.
-- source:
--   Wiles, Ann. of Math. 141 (1995); Taylor–Wiles, Ann. of Math. 141 (1995); Breuil–Conrad–Diamond–Taylor, J. Amer. Math. Soc. 14 (2001); Thorne survey Theorem 4.1

import Mathlib
import Definitions.Def_NumberFieldModularity_setup
open NumberFieldModularity

namespace NumberFieldModularity
theorem modularity_over_Q (D : ModularitySetup) (hQ : D.K_is_Q) : ∃ (n : D.Level) (c : D.Coh n), c ≠ 0 ∧ ∃ S : Finset D.Place, ∀ v ∉ S, D.hecke n v c = D.a v • c := by sorry
end NumberFieldModularity
