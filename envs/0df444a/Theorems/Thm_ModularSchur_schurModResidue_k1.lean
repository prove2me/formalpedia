-- Prove2me | Theorems.Thm_ModularSchur_schurModResidue_k1
-- name    : ModularSchur.schurModResidue_k1
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-19T22:49:46.601795+00:00
-- url     : https://prove2.me/theorems/90f6b5e7-1ec1-4741-85ce-62ff8dc37d4e
-- title:
--   One colour: $S_m(1,\ell) = \min(\ell-1, \lfloor m/\ell \rfloor)$ for $2 \le \ell \le m$
-- statement:
--   This is the exact single-colour modular Schur number in the range the literature posed it for.
--
--   For every $m \ge 2$ and every $\ell$ with $2 \le \ell \le m$,
--
--   $$ \mathrm{schurModResidue}(m,1,\ell) = \min\!\left(\ell - 1, \left\lfloor \frac{m}{\ell} \right\rfloor\right). $$
--
--   The two terms are the two ways a single class can fail. The term $\ell - 1$ is the no-wrap regime, where the class is defeated by $\ell$ copies of $1$ summing to $\ell$; the term $\lfloor m/\ell \rfloor$ is the wrap regime, where some $\ell$-tuple sums past the modulus and lands back at $\overline{1}$. Which one binds depends on whether $\ell(\ell-1) < m$.
--
--   This is one of the two regimes of the problem that admit an exact formula, the other being the many-colours regime of the main closed form; the intermediate range $1 < k < n-1$ has no known formula.
-- source:
--   McKenna 2026, "Prime-power structure of the stable regime for modular Schur numbers", docs/paper/modular-schur.pdf in the same repository, Theorem 6.1 (the $k=1$ case). Prior art: the paper states "This resolves [DSWH2025, Problem 1, part 3]"; see D'orville, Sim, Wong and Ho, "Modular generalizations of Schur numbers", Integers 25 (2025) #A62, https://math.colgate.edu/~integers/z62/z62.pdf. Lean source: https://github.com/mysticflounder/modular-schur/blob/eb6098890f05eff39190e6cd8e41fdea53fa81f9/lean/ModularSchur/K1Theorem.lean#L173-L200

import Definitions.Def_ModularSchurBasic
import Definitions.Def_ModularSchurPartition
import Mathlib

open ModularSchur
open Finset Classical
variable {m ℓ : ℕ}

theorem ModularSchur.schurModResidue_k1 (m ℓ : ℕ) (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ) (hlm : ℓ ≤ m) :
    schurModResidue m 1 ℓ = min (ℓ - 1) (m / ℓ) := by sorry
