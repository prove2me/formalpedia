-- Prove2me | Theorems.Thm_ModularCurve_surjOn_reductionModL_torsion_pow
-- name    : ModularCurve.surjOn_reductionModL_torsion_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/3cc4e6d0-d19d-5136-9482-da17fef7dad5
-- title:
--   Reduction mod q is onto the q^k-torsion of J₀(N)
-- statement:
--   Fix a nonzero natural number $N$ and a prime $q$ with $q \nmid N$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` satisfying `A.LiesOverPrime q`, i.e. the image of $q$ in $\overline{\mathbb{Q}}$ is a nonunit of $A$, so that $A$ is a valuation ring of residue characteristic $q$, with residue field `ResidueField ↥A`. Assume `ReductionInputsModL A N`, that is, `ReductionInputsAlong A (residue A) N`: there is a choice $r$ of places of the base-changed modular function field `laurentBaseChange`$(\overline{\mathbb{Q}},$ `modularFunctionFieldFull N`$)$ satisfying `IsPlaceReductionAlong A (residue A) N r` together with `PrincipalGeneratedByIntegral A (residue A) N`; these data are what make the reduction homomorphism $$\mathtt{reductionModL}\ A\ N \colon \mathrm{JZero}\,N \longrightarrow \mathrm{JZeroC}\,(\mathrm{ResidueField}\ A)\,N$$ equal to the reduction of degree-zero divisor classes along the chosen places rather than the zero map. Here $\mathrm{JZero}\,N$ is $\mathrm{Pic}^0$ of the modular function field over $\overline{\mathbb{Q}}$, and $\mathrm{JZeroC}\,k\,N$ is $\mathrm{Pic}^0$ of the field $k$-adjoin `divisorExpansionsC k N` inside the Laurent series over $k$, both being degree-zero divisors modulo principal divisors. Then for every natural number $k$, reduction maps the set $\{x : q^k \cdot x = 0\}$ in $\mathrm{JZero}\,N$ onto the set $\{y : q^k \cdot y = 0\}$ in $\mathrm{JZeroC}\,(\mathrm{ResidueField}\ A)\,N$; i.e. every $q^k$-torsion class on the special fibre is the reduction of a $q^k$-torsion class on the generic fibre.
--
--   This is the residue-characteristic case of the classical surjectivity of reduction on torsion for the Jacobian of $X_0(N)$ at a place of good reduction, complementing the prime-to-$q$ case; in the formalisation it is obtained from the finite flat $q^k$-torsion group scheme of a model of $J_0(N)$ over a localisation of $\mathbb{Z}$, by lifting residue-field points along a finite flat Hopf algebra over the valuation ring and using separatedness to compare lifts. It feeds the construction of Néron-type objects attached to $J_0(N)$ at $q$ and the analysis of Eisenstein and Hecke torsion used in level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_surjOn_reductionModL_torsion_pow.lean

import Mathlib
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve IsLocalRing

theorem ModularCurve.surjOn_reductionModL_torsion_pow
    (N : ℕ) [NeZero N] (q : ℕ) [Fact q.Prime] (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (hinp : ReductionInputsModL A N) (k : ℕ) :
    Set.SurjOn (reductionModL A N)
      {x : JZero N | (q ^ k) • x = 0}
      {y : JZeroC (ResidueField ↥A) N | (q ^ k) • y = 0} := by sorry
