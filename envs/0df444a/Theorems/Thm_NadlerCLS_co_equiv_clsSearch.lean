-- Prove2me | Theorems.Thm_NadlerCLS_co_equiv_clsSearch
-- name    : NadlerCLS.co_equiv_clsSearch
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:03:26.72626+00:00
-- url     : https://prove2.me/theorems/a6be6983-3c56-4110-87c1-64d5b5c87dd9
-- title:
--   The choice of $\ell_1$ and of two circuits is inessential: Definition 2 $\equiv_p$ canonical 3D Continuous-LocalOpt
-- statement:
--   Continuous-LocalOpt on $[0,1]^3$ as printed in Definition 2 (circuits $f$ and $p$, $\ell_1$ norm) and the canonical three-dimensional Continuous-LocalOpt (one circuit computing $p$ and the three coordinates of $f$, Lipschitz violations measured in the max norm) reduce to each other by polynomial-time many-one reductions:
--   $$ \text{Continuous-LocalOpt}_{\ell_1}\ \equiv_p\ \text{Continuous-LocalOpt}_{\ell_\infty}. $$
--
--   The class CLS consists of the total search problems reducing to Continuous-LocalOpt; this equivalence shows that the paper's Definition 2 defines the same class as the canonical problem.
--
--   Differences from the source:
--   - reading: "the choice of $[0,1]^3$ and $\ell_1$ norms is inessential" (a remark citing [DP11]) → mutual polynomial-time reductions between Definition 2 at $n=3$ and the public canonical `clsSearch` (one shared circuit, max norm); reason: the platform's CLS is defined through `clsSearch`; this is the part of the remark that the classification of Definition-2-based problems needs
-- source:
--   Xiong–Vlatakis-Gkaragkounis, On the Complexity of Finding Fixed Points for Set-Valued Contractions, arXiv:2609.14101 (held version of 2026-11-03, sha256 1fcc5a027ffe65205e4ef9a9ef7730f6f07fe3f7006447cac39a7562e36dc485), Section 3, p.11 ("the choice of [0, 1]3 and ℓ1 norms is inessential")

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity
import Definitions.Def_NadlerCLS_coSearch

set_option autoImplicit false

namespace NadlerCLS

open NetworkEquilibriumCLS.LinearNash

/-- **The choice of the ℓ₁ norm and of two circuits is inessential in dimension three**
(Xiong–Vlatakis-Gkaragkounis, *On the Complexity of Finding Fixed Points for Set-Valued
Contractions*, arXiv:2609.14101, held version of 2026-11-03, sha256 1fcc5a02…6dc485, Section 3,
p.11: "As discussed in [DP11], the choice of [0, 1]3 and ℓ1 norms is inessential"). Continuous-LocalOpt
on `[0, 1]³` as printed in Definition 2 (two circuits, ℓ₁ norm) and the public canonical
three-dimensional Continuous-LocalOpt `clsSearch` (one shared circuit, max norm) reduce to each
other by polynomial-time search reductions.

**Formalization Note** `clsSearch` is the class-defining problem of the public `InCLS`; this item
connects the paper's Definition 2 to it. -/
theorem co_equiv_clsSearch :
    SearchReduces (coSearch 3) clsSearch ∧ SearchReduces clsSearch (coSearch 3) := by sorry

end NadlerCLS
