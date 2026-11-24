-- Prove2me | Theorems.Thm_Leopoldt_exists_finiteIndex_units_ball
-- name    : Leopoldt.exists_finiteIndex_units_ball
-- status  : Proved
-- author  : @wojtek_politarczyk
-- created : 2026-11-24T11:03:47.303808+00:00
-- url     : https://prove2.me/theorems/c300c297-f759-4bb5-a4ef-8b69285f645d
-- title:
--   Existence of a finite-index unit system in the $p^2$-ball
-- statement:
--   Let $p$ be a prime and $\mathbb{K}$ a number field with unit group $E = \mathcal{O}(\mathbb{K})^\times$ of Dirichlet rank $r$. Then there exists a family of $r$ units $u_1, \dots, u_r \in E$ generating a finite-index subgroup of $E$ such that for every $i$ and every prime $\wp \mid p$, $$\|\iota(u_i)_\wp - 1\|_\wp \le \|p\|_\wp^2.$$
--
--   This follows by lifting a $\mathbb{Z}$-basis of $E / \mu(\mathbb{K})$ and raising each generator to the exponent of the finite unit group $(\mathcal{O}(\mathbb{K}) / p^2 \mathcal{O}(\mathbb{K}))^\times$.
-- source:
--   Standard algebraic number theory; cf. M. Waldschmidt, Transcendance et exponentielles en plusieurs variables, Invent. Math. 63 (1981), 97-127

import Definitions.Def_LeopoldtDefect

open NumberField

namespace Leopoldt

theorem exists_finiteIndex_units_ball (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] :
    ∃ u : Fin (Units.rank K) → (𝓞 K)ˣ,
      (Subgroup.closure (Set.range u)).FiniteIndex ∧
      ∀ (i : Fin (Units.rank K)) (v : PrimesOver p K),
        ‖((diagonalUnits p K (u i) v : v.1.adicCompletionIntegers K) :
          v.1.adicCompletion K) - 1‖ ≤ ‖((p : ℕ) : v.1.adicCompletion K)‖ ^ 2 := by sorry

end Leopoldt
