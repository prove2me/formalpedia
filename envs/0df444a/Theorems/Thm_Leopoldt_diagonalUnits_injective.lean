-- Prove2me | Theorems.Thm_Leopoldt_diagonalUnits_injective
-- name    : Leopoldt.diagonalUnits_injective
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T02:41:33.879983+00:00
-- url     : https://prove2.me/theorems/d1e6bbde-67ce-47ca-badc-651ce1c382eb
-- title:
--   The diagonal embedding $\iota : E \to U$ is injective
-- statement:
--   Let $K$ be a number field and $p$ a prime. The diagonal map
--   $$\iota : \mathcal{O}_K^\times \longrightarrow U = \prod_{\wp \mid p} \mathcal{O}_\wp^\times$$
--   from the global units into the semilocal units at $p$ is injective.
--
--   This holds because there is at least one prime $\wp$ above $p$ and the completion map $K \to K_\wp$ is an injective field homomorphism.
-- source:
--   P. Mihailescu, On CM Z_p-extensions and the Leopoldt conjecture for CM fields, arXiv:1105.4544, Section 1.1 (the diagonal embedding iota : K -> K_p); mission definition file Def_LeopoldtDefect (diagonalUnits)

import Definitions.Def_LeopoldtDefect

open NumberField

namespace Leopoldt
theorem diagonalUnits_injective (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K] :
    Function.Injective (diagonalUnits p K) := by sorry
end Leopoldt
