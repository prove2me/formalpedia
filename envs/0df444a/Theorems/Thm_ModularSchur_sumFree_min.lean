-- Prove2me | Theorems.Thm_ModularSchur_sumFree_min
-- name    : ModularSchur.sumFree_min
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-19T22:48:31.580949+00:00
-- url     : https://prove2.me/theorems/f8f90c9c-5771-4d42-9c20-017b7c426530
-- title:
--   The interval up to $\min(\ell-1, \lfloor m/\ell \rfloor)$ is $\ell$-sum-free
-- statement:
--   This is the witness that makes the one-colour formula attainable.
--
--   Let $m \ge 2$ and $2 \le \ell \le m$, and set $N^{*} = \min\!\big(\ell - 1, \lfloor m/\ell \rfloor\big)$. Then
--
--   $$ \{\overline{1}, \overline{2}, \dots, \overline{N^{*}}\} \subseteq \mathbb{Z}/m \text{ is } \ell\text{-sum-free modulo } m. $$
--
--   At this length the integer sums of $\ell$ elements drawn from $[1, N^{*}]$ all lie in $[\ell, m]$, so their residues avoid the interval itself.
--
--   This single set realises the one-colour value, so it is the lower bound matching the two upper bounds and the reason the formula is an exact minimum rather than an estimate.
-- source:
--   McKenna 2026, "Prime-power structure of the stable regime for modular Schur numbers", docs/paper/modular-schur.pdf in the same repository, the lower-bound witness in the proof of Theorem 6.1. Lean source: https://github.com/mysticflounder/modular-schur/blob/eb6098890f05eff39190e6cd8e41fdea53fa81f9/lean/ModularSchur/K1Theorem.lean#L130-L171

import Definitions.Def_ModularSchurBasic
import Definitions.Def_ModularSchurPartition
import Mathlib

open ModularSchur
open Finset Classical
variable {m ℓ : ℕ}

theorem ModularSchur.sumFree_min (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ) (hlm : ℓ ≤ m) :
    IsEllSumFree m ℓ (stableResidues m (min (ℓ - 1) (m / ℓ))) := by sorry
