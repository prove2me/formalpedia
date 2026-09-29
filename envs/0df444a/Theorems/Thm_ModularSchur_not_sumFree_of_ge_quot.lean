-- Prove2me | Theorems.Thm_ModularSchur_not_sumFree_of_ge_quot
-- name    : ModularSchur.not_sumFree_of_ge_quot
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-19T22:46:35.941987+00:00
-- url     : https://prove2.me/theorems/aa71c018-8765-429a-901e-4dc8ce85ad34
-- title:
--   For $N \ge \lfloor m/\ell \rfloor + 1$ the residue interval is not $\ell$-sum-free
-- statement:
--   This is the second and harder upper bound behind the one-colour formula.
--
--   Let $m \ge 2$ and $2 \le \ell \le m$, and suppose $N \ge \lfloor m/\ell \rfloor + 1$. Then the residue interval $\mathrm{stableResidues}(m,N) = \{\overline{1}, \dots, \overline{N}\}$ is **not** $\ell$-sum-free modulo $m$:
--
--   $$ N \ge \left\lfloor \frac{m}{\ell} \right\rfloor + 1 \implies \neg\,\big(\{\overline{1}, \dots, \overline{N}\} \text{ is } \ell\text{-sum-free modulo } m\big). $$
--
--   The obstruction comes from wrap-around: once the interval is this long, some $\ell$-tuple drawn from $[1,N]$ has integer sum $m + 1$, which is congruent to $1$ modulo $m$, and $\overline{1}$ lies in the interval.
--
--   This is the branch that supplies the $\lfloor m/\ell \rfloor$ term of the one-colour formula, and it is what makes that formula a minimum of two competing quantities rather than a single expression.
-- source:
--   McKenna 2026, "Prime-power structure of the stable regime for modular Schur numbers", docs/paper/modular-schur.pdf in the same repository, the wrap-around upper bound in the proof of Theorem 6.1. Lean source: https://github.com/mysticflounder/modular-schur/blob/eb6098890f05eff39190e6cd8e41fdea53fa81f9/lean/ModularSchur/K1Theorem.lean#L71-L128

import Definitions.Def_ModularSchurBasic
import Definitions.Def_ModularSchurPartition
import Mathlib

open ModularSchur
open Finset Classical
variable {m ℓ : ℕ}

theorem ModularSchur.not_sumFree_of_ge_quot (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ) (hlm : ℓ ≤ m) {N : ℕ}
    (hN : m / ℓ + 1 ≤ N) : ¬ IsEllSumFree m ℓ (stableResidues m N) := by sorry
