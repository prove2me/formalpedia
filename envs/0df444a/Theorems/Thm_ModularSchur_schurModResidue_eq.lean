-- Prove2me | Theorems.Thm_ModularSchur_schurModResidue_eq
-- name    : ModularSchur.schurModResidue_eq
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-19T22:52:19.192804+00:00
-- url     : https://prove2.me/theorems/77a6db49-606c-4283-b7d2-b57fc3593ee9
-- title:
--   Closed form at residue level: $\mathrm{schurModResidue}(m,k,\ell) = n - 1$
-- statement:
--   This is the closed form for the residue-level modular Schur number in the many-colours regime.
--
--   Throughout, $m \ge 2$ is the modulus, $\ell \ge 2$ the number of summands, $k \ge 1$ the number of colour classes, $d = \gcd(m, \ell - 1)$ and $n = m/d$.
--
--   For every $m \ge 2$, every $\ell \ge 2$, and every $k \ge n - 1$,
--
--   $$ \mathrm{schurModResidue}(m,k,\ell) = \frac{m}{\gcd(m, \ell - 1)} - 1. $$
--
--   The value is obtained by combining the uniform upper bound with the singleton-colouring lower bound, which meet exactly.
--
--   This is the residue-level form of the mission's headline identity. It is stated separately from the integer-level version because the residue side is where the argument lives, and because a consumer already working in the cyclic group can use it without passing through the reduction theorem.
-- source:
--   McKenna 2026, "Prime-power structure of the stable regime for modular Schur numbers", docs/paper/modular-schur.pdf in the same repository, Theorem 1.2 (main closed form), residue level. Lean source: https://github.com/mysticflounder/modular-schur/blob/eb6098890f05eff39190e6cd8e41fdea53fa81f9/lean/ModularSchur/Partition.lean#L97-L102

import Definitions.Def_ModularSchurPartition
import Mathlib

open ModularSchur
open Finset
variable {m : ℕ}

theorem ModularSchur.schurModResidue_eq (m k ℓ : ℕ) (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ)
    (hk : m / Nat.gcd m (ℓ - 1) - 1 ≤ k) :
    schurModResidue m k ℓ = m / Nat.gcd m (ℓ - 1) - 1 := by sorry
