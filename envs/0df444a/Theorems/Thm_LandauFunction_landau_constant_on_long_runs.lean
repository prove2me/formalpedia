-- Prove2me | Theorems.Thm_LandauFunction_landau_constant_on_long_runs
-- name    : LandauFunction.landau_constant_on_long_runs
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:28:28.573733+00:00
-- url     : https://prove2.me/theorems/1a6331fa-0346-4f69-94b1-660d721f9f83
-- title:
--   Landau's function is constant on arbitrarily long runs (Nicolas 1968)
-- statement:
--   There are arbitrarily long sequences of consecutive integers on which Landau's function is constant: for every $m\in\mathbb N$ there exists $n\in\mathbb N$ such that
--
--   $$g(n)=g(n+1)=\dots=g(n+m).$$
--
--   This shows that $g$, although of growth $e^{(1+o(1))\sqrt{n\ln n}}$, has arbitrarily long plateaus.
-- source:
--   J.-L. Nicolas, Sur l'ordre maximum d'un élément dans le groupe Sn des permutations, Acta Arith. 14 (1968) 315–332; as quoted in Wikipedia, "Landau's function", revision oldid=1303222269 (https://en.wikipedia.org/w/index.php?title=Landau%27s_function&oldid=1303222269), second paragraph, ref. [1].

import Mathlib
import Definitions.Def_LandauFunction_landau

namespace LandauFunction
theorem landau_constant_on_long_runs :
    ∀ m : ℕ, ∃ n : ℕ, ∀ k ≤ m, landau (n + k) = landau n := by sorry
end LandauFunction
