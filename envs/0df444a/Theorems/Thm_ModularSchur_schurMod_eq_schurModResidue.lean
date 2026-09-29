-- Prove2me | Theorems.Thm_ModularSchur_schurMod_eq_schurModResidue
-- name    : ModularSchur.schurMod_eq_schurModResidue
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-19T22:51:06.684645+00:00
-- url     : https://prove2.me/theorems/95ae9e7a-9e6f-4a8f-a011-210dc7dd3291
-- title:
--   Residue reduction: $S_m(k,\ell)$ equals its residue-level counterpart
-- statement:
--   This is the residue reduction theorem, which identifies the integer-level and residue-level modular Schur numbers.
--
--   Let $m \ge 2$ and let $k, \ell$ be arbitrary. Then
--
--   $$ S_m(k,\ell) = \mathrm{schurModResidue}(m,k,\ell), $$
--
--   where the left side counts colourings of the integer interval $[1,N]$ and the right side counts colourings of the residue set $\{\overline{1}, \dots, \overline{N}\} \subseteq \mathbb{Z}/m$.
--
--   This is the hinge of the development. Every bound in the mission is proved on the residue side, where the group structure is available, and then quoted on the integer side, which is where the modular Schur number is defined and where the literature's values live. Without this identification the two families of results would not be about the same number.
-- source:
--   McKenna 2026, "Prime-power structure of the stable regime for modular Schur numbers", docs/paper/modular-schur.pdf in the same repository, Lemma 2.1 (Residue reduction). Lean source: https://github.com/mysticflounder/modular-schur/blob/eb6098890f05eff39190e6cd8e41fdea53fa81f9/lean/ModularSchur/IntegerBridge.lean#L152-L162

import Definitions.Def_ModularSchurIntegerBridge
import Definitions.Def_ModularSchurPartition
import Mathlib

open ModularSchur
open Finset
variable {m : ℕ}

theorem ModularSchur.schurMod_eq_schurModResidue (m k ℓ : ℕ) (hm : 2 ≤ m) :
    schurMod m k ℓ = schurModResidue m k ℓ := by sorry
