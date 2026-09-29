-- Prove2me | Theorems.Thm_ModularSchur_le_schurModResidue
-- name    : ModularSchur.le_schurModResidue
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-19T22:49:19.775457+00:00
-- url     : https://prove2.me/theorems/a8657a35-acbe-43e3-b476-87671f21236b
-- title:
--   Lower bound: $m/\gcd(m,\ell-1) - 1 \le S_m(k,\ell)$ once $k \ge n-1$
-- statement:
--   This is the lower half of the closed form, proved at the level of residues.
--
--   Throughout, $m \ge 2$ is the modulus, $\ell \ge 2$ the number of summands, $k \ge 1$ the number of colour classes, $d = \gcd(m, \ell - 1)$ and $n = m/d$.
--
--   For every $m \ge 2$ and $\ell \ge 2$, if at least $n - 1$ colours are available, that is if $k \ge n - 1$, then
--
--   $$ n - 1 = \frac{m}{\gcd(m, \ell - 1)} - 1 \le \mathrm{schurModResidue}(m,k,\ell). $$
--
--   The hypothesis $k \ge n-1$ is exactly what the witnessing colouring costs: give each of the residues $\overline{1}, \overline{2}, \dots, \overline{n-1}$ its own class, and pad with empty classes. Each such singleton is $\ell$-sum-free because none of $1, \dots, n-1$ is a multiple of $n$.
--
--   This is the constructive half of the mission: together with the uniform upper bound it pins the value exactly, and it is what identifies $k \ge n-1$ as a sufficient supply of colours.
-- source:
--   McKenna 2026, "Prime-power structure of the stable regime for modular Schur numbers", docs/paper/modular-schur.pdf in the same repository, Theorem 4.1 (lower bound), residue level. Lean source: https://github.com/mysticflounder/modular-schur/blob/eb6098890f05eff39190e6cd8e41fdea53fa81f9/lean/ModularSchur/Partition.lean#L75-L95

import Definitions.Def_ModularSchurBasic
import Definitions.Def_ModularSchurPartition
import Mathlib

open ModularSchur
open Finset Nat
variable {m ℓ : ℕ}

theorem ModularSchur.le_schurModResidue (m k ℓ : ℕ) (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ)
    (hk : m / Nat.gcd m (ℓ - 1) - 1 ≤ k) :
    m / Nat.gcd m (ℓ - 1) - 1 ≤ schurModResidue m k ℓ := by sorry
