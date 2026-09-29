-- Prove2me | Theorems.Thm_ModularCurve_exists_mem_torsionBy_eisensteinQuotientMk_eq
-- name    : ModularCurve.exists_mem_torsionBy_eisensteinQuotientMk_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/1c2ebf62-4b61-5890-a58f-4b7c69be8cb9
-- title:
--   Lifting m-torsion along the Eisenstein quotient map
-- statement:
--   Fix a natural number $p$, nonzero, and write $J =$ [`ModularCurve.JZero p`](def/ModularCurve_ArithmeticGalois.html#L115) for the degree-zero part of the divisor class group $\mathrm{Pic}^0$ of the field `modularFunctionFieldBar p`, the base change to $\overline{\mathbf Q}$ of the full modular function field of level $p$, over $\overline{\mathbf Q}$ — i.e. degree-zero divisors modulo principal divisors. Let $iJ$ be a module structure on $J$ over [`ModularCurve.HeckeAlg`](def/HeckeGalois_EichlerShimura.html#L14), the polynomial ring $\mathbf Z[X_\ell : \ell \text{ prime}]$ in indeterminates indexed by the primes; with respect to it, let $\gamma J \subseteq J$ be `eisensteinKernelSubmodule p iJ`, the Hecke submodule obtained by acting on all of $J$ by the set `eisensteinKernel (JZero p) (eisensteinIdeal p)`, and let $\tilde J = J/\gamma J$ be the Eisenstein quotient, with quotient map `eisensteinQuotientMk p iJ` $: J \to_+ \tilde J$. Let $m$ be a nonzero integer and let $z \in \tilde J$ satisfy $m \cdot z = 0$, i.e. $z$ lies in the $\mathbf Z$-torsion submodule `Submodule.torsionBy ℤ _ m`. Then there exists $x \in J$ with $m \cdot x = 0$ whose image under `eisensteinQuotientMk p iJ` is $z$.
--
--   This is the algebraic step presenting the $m$-torsion of Mazur's Eisenstein quotient as a quotient of the $m$-torsion of $J_0(p)$: the surjection $J \to \tilde J$ remains surjective on $m$-torsion, so $\tilde J[m] = J[m]/(J[m] \cap \gamma J)$. It is used in the construction of finite flat models for torsion in the Eisenstein quotient and their reductions modulo a prime $\ell \neq 2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_mem_torsionBy_eisensteinQuotientMk_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Definitions.Def_ModularCurve_HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.exists_mem_torsionBy_eisensteinQuotientMk_eq
    (p : ℕ) [NeZero p] (iJ : Module ModularCurve.HeckeAlg (ModularCurve.JZero p))
    (m : ℤ) (hm : m ≠ 0)
    (z : ModularCurve.EisensteinQuotient p iJ)
    (hz : z ∈ Submodule.torsionBy ℤ (ModularCurve.EisensteinQuotient p iJ) m) :
    ∃ x : ModularCurve.JZero p, x ∈ Submodule.torsionBy ℤ (ModularCurve.JZero p) m ∧
      ModularCurve.eisensteinQuotientMk p iJ x = z := by sorry
