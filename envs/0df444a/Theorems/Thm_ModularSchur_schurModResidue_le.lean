-- Prove2me | Theorems.Thm_ModularSchur_schurModResidue_le
-- name    : ModularSchur.schurModResidue_le
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-19T22:50:44.025569+00:00
-- url     : https://prove2.me/theorems/978dbb2c-7ca3-4b3f-ab9e-aa5c3df01949
-- title:
--   Upper bound: $S_m(k,\ell) \le m/\gcd(m,\ell-1) - 1$
-- statement:
--   This is the upper half of the closed form, proved at the level of residues.
--
--   Throughout, $m \ge 2$ is the modulus, $\ell \ge 2$ the number of summands, $k \ge 1$ the number of colour classes, $d = \gcd(m, \ell - 1)$ and $n = m/d$.
--
--   For every $m \ge 2$, $\ell \ge 2$ and every number of colours $k$,
--
--   $$ \mathrm{schurModResidue}(m,k,\ell) \le \frac{m}{\gcd(m, \ell - 1)} - 1 = n - 1. $$
--
--   No hypothesis on $k$ is needed: the bound holds uniformly, however many colours are available. The reason is that once the interval reaches $n$, whichever class receives the residue $\overline{n}$ fails to be $\ell$-sum-free, and adding colours does not help.
--
--   Uniformity in $k$ is what makes this the ceiling of the whole problem, and it is half of the closed form: the matching lower bound only needs enough colours to be available.
-- source:
--   McKenna 2026, "Prime-power structure of the stable regime for modular Schur numbers", docs/paper/modular-schur.pdf in the same repository, Theorem 3.1 (upper bound), residue level. Prior art: the paper records in Remark 3.2 that "Equivalently, this is [DSWH2025, Corollary 3] applied at $a = n$"; see D'orville, Sim, Wong and Ho, "Modular generalizations of Schur numbers", Integers 25 (2025) #A62, https://math.colgate.edu/~integers/z62/z62.pdf. Lean source: https://github.com/mysticflounder/modular-schur/blob/eb6098890f05eff39190e6cd8e41fdea53fa81f9/lean/ModularSchur/Partition.lean#L51-L69

import Definitions.Def_ModularSchurBasic
import Definitions.Def_ModularSchurPartition
import Mathlib

open ModularSchur
open Finset Nat
variable {m ℓ : ℕ}

theorem ModularSchur.schurModResidue_le (m k ℓ : ℕ) (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ) :
    schurModResidue m k ℓ ≤ m / Nat.gcd m (ℓ - 1) - 1 := by sorry
