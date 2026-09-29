-- Prove2me | Theorems.Thm_ModularCurve_charLDegeneracyRoof_eq_modularFunctionFieldC_mul
-- name    : ModularCurve.charLDegeneracyRoof_eq_modularFunctionFieldC_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/772e5a06-f839-5181-8592-f106b99e54b6
-- title:
--   The ℓ-roof equals the level-Nℓ modular function field
-- statement:
--   Let $\kappa$ be a field, $p$ a prime with $\kappa$ of characteristic $p$, let $N \ge 1$ be a natural number and $\ell$ a prime, and assume $p \nmid N$ and $p \neq \ell$. Inside the field $\kappa((q))$ of Laurent series over $\kappa$, write $\tilde j =$ `jqModC` $\kappa$ for the series $q^{-1}$ times the image under $\mathbb{Z} \to \kappa$ of the integral power series `jNum` (the $q$-expansion of the modular invariant $j$), and for $d \ge 1$ write $\tilde j_d =$ `jqNModC` $\kappa\,d$ for its image under the substitution $q \mapsto q^{d}$. The assertion is an equality of intermediate fields of $\kappa((q))$ over $\kappa$: the $\ell$-degeneracy roof at level $N$, by definition the subfield generated over $\kappa$ by the four elements $\tilde j, \tilde j_N, \tilde j_\ell, \tilde j_{N\ell}$, coincides with the modular function field of level $N\ell$, by definition the subfield generated over $\kappa$ by the two elements $\tilde j$ and $\tilde j_{N\ell}$.
--
--   This identifies the field on which the two degeneracy embeddings of the level-$N$ modular function field both land with the full level-$N\ell$ function field, in the setting where the residue characteristic $p$ divides neither $N$ nor $\ell$. It is used in the analysis of Hecke correspondences at $\ell$ in characteristic $p$, in particular by the statements about specialisation of places and restriction of the Hecke operators $\alpha$ and $\beta$ along the degeneracy maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_charLDegeneracyRoof_eq_modularFunctionFieldC_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_CharLDegeneracyHecke

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.charLDegeneracyRoof_eq_modularFunctionFieldC_mul
    (κ : Type*) [Field κ] (p : ℕ) [Fact p.Prime] [CharP κ p]
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] (hpN : ¬ p ∣ N) (hpℓ : p ≠ ℓ) :
    ModularCurve.charLDegeneracyRoof κ N ℓ = ModularCurve.modularFunctionFieldC κ (N * ℓ) := by sorry
