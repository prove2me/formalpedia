-- Prove2me | Theorems.Thm_ModularSchur_singleton_sumFree_iff
-- name    : ModularSchur.singleton_sumFree_iff
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-19T22:47:54.394419+00:00
-- url     : https://prove2.me/theorems/5448761e-2b19-4eff-ad10-33f46f8830e2
-- title:
--   Singleton safety: $\{r\}$ is $\ell$-sum-free iff $(\ell-1)r \not\equiv 0$
-- statement:
--   This is the singleton safety criterion, the elementary test that drives every bound in the mission.
--
--   Let $m$ be a modulus, let $\ell \ge 1$, and let $r \in \mathbb{Z}/m$ be a residue. The one-element class $\{r\}$ is $\ell$-sum-free modulo $m$ exactly when
--
--   $$ (\ell - 1)\, r \ne 0 \quad \text{in } \mathbb{Z}/m. $$
--
--   The reason is immediate: the only $\ell$-fold sum available inside $\{r\}$ is $\ell r$, and the only possible target is $r$ itself, so the class fails precisely when $\ell r = r$.
--
--   Singletons are the cheapest possible colour classes, so this criterion is what decides how far an all-singletons colouring can reach. It is used in both directions throughout the mission: to certify that small residues are safe, and to exhibit the one residue that is not.
--
--   **Formalization Note** The cast $(\ell : \mathbb{Z}/m)$ is the image of the natural number $\ell$, so the left-hand factor is written $(\ell : \mathbb{Z}/m) - 1$ rather than as a cast of $\ell - 1$; the two agree because $\ell \ge 1$.
-- source:
--   McKenna 2026, "Prime-power structure of the stable regime for modular Schur numbers", docs/paper/modular-schur.pdf in the same repository, Lemma 2.3 (Singleton safety). Prior art: the paper states "This is [DSWH2025, Theorem 4] rewritten in the variables natural for our application"; see D'orville, Sim, Wong and Ho, "Modular generalizations of Schur numbers", Integers 25 (2025) #A62, https://math.colgate.edu/~integers/z62/z62.pdf. Lean source: https://github.com/mysticflounder/modular-schur/blob/eb6098890f05eff39190e6cd8e41fdea53fa81f9/lean/ModularSchur/SingletonSafety.lean#L20-L24

import Definitions.Def_ModularSchurBasic
import Mathlib

open ModularSchur
open Finset
variable {m : ℕ}

theorem ModularSchur.singleton_sumFree_iff (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (r : ZMod m) :
    IsEllSumFree m ℓ {r} ↔ ((ℓ : ZMod m) - 1) * r ≠ 0 := by sorry
