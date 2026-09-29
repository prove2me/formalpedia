-- Prove2me | Theorems.Thm_KobayashiMaskawa1973_rephasingEquiv_quartet_invariant
-- name    : KobayashiMaskawa1973.rephasingEquiv_quartet_invariant
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T18:16:49.243072+00:00
-- url     : https://prove2.me/theorems/55cbef69-e332-4929-8843-fb6d87fc29ce
-- title:
--   Plaquette quartet product is invariant under rephasing
-- statement:
--   Let $U, V \in \mathrm{M}_3(\mathbb{C})$ be two matrices that are rephasing equivalent, meaning $V = \operatorname{diag}(e^{ia}) U \operatorname{diag}(e^{ib})$ for some real phase vectors $a, b \in \mathbb{R}^3$. Then the $2 \times 2$ quartet product on the first two rows and columns is strictly invariant:
--
--   $$V_{00} V_{11} V_{01}^* V_{10}^* = U_{00} U_{11} U_{01}^* U_{10}^*.$$
--
--   This holds because the rephasing factors multiply each entry by $V_{jk} = e^{i(a_j + b_k)} U_{jk}$, yielding the total phase factor $e^{i(a_0 + b_0 + a_1 + b_1 - a_0 - b_1 - a_1 - b_0)} = e^0 = 1$.
-- source:
--   C. Jarlskog, Commutator of the Quark Mass Matrices in the Standard Electroweak Model and a Measure of Maximal CP Violation, Phys. Rev. Lett. 55 (1985) 1039

import Mathlib
import Definitions.Def_KobayashiMaskawa1973_Defs

open Matrix

namespace KobayashiMaskawa1973

theorem rephasingEquiv_quartet_invariant (U V : Matrix (Fin 3) (Fin 3) ℂ) (h : RephasingEquiv U V) :
    V 0 0 * V 1 1 * star (V 0 1) * star (V 1 0) = U 0 0 * U 1 1 * star (U 0 1) * star (U 1 0) := by sorry

end KobayashiMaskawa1973
