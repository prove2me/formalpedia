-- Prove2me | Theorems.Thm_ModularCurve_mazurQuotientSpecialization_heckeModuleBar
-- name    : ModularCurve.mazurQuotientSpecialization_heckeModuleBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/b54e1b79-d6cc-5245-98b4-e77ce2bd53fd
-- title:
--   Specialisation of the Eisenstein quotient away from p
-- statement:
--   Let $p$ be a prime (supplied as `Fact p.Prime`) and assume `hcomm : HeckeOperatorsCommuteBar p`, i.e. that the operators `heckeOperatorBar p ℓ` on `JZero p` commute pairwise; then `heckeModuleBar p`, which is defined by cases and equals the action of `HeckeAlg` through `heckeEvalBar hcomm` (with `heckeGen ℓ` acting as `heckeOperatorBar p ℓ`) exactly when that commutation holds, is a genuine Hecke-module structure on `JZero p`. The conclusion is the project's predicate `MazurQuotientSpecialization p (heckeModuleBar p)`, which unfolds as follows: for every prime $\ell \ne p$ and every valuation subring $A$ of $\overline{\mathbb Q}$ with `A.LiesOverPrime ℓ`, there exist a type $T$, an additive group structure on it, and an additive map $s$ from the Eisenstein quotient `EisensteinQuotient p (heckeModuleBar p)` $=$ `JZero p` modulo `eisensteinKernel (JZero p) (eisensteinIdeal p) • ⊤` to $T$, such that three clauses hold for the set `eisensteinQuotientRational p (heckeModuleBar p)` of classes coming from $x \in$ `JZero p` with $\sigma \cdot x - x$ in that submodule for all $\sigma \in \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$: (i) such a class $z$ killed by some $m \in \mathbb N$ with $\ell \nmid m$ and with $s z = 0$ is zero; (ii) if $\ell \ne 2$, such a $z$ killed by some $\ell^k$ and with $s z = 0$ is zero; (iii) a cusp rule: for every place $x$ of `modularFunctionFieldBar p` and $j_1, j_2 \in \overline{\mathbb Q}$, given that the divisors $(x) - (\bar\infty)$ and $(x) - (\bar 0)$ have degree zero, that $x$ is fixed by the arithmetic Galois action of every $\sigma$, that `x.ord` of `jBar p` $- j_1$ and of `jpBar p` $- j_2$ are positive, and that `A.valuation` $j_1 > 1$, one has: if `A.valuation` $j_2 =$ `A.valuation` $j_1^{\,p}$ then $s$ kills the class of $(x) - (\bar\infty)$, and if `A.valuation` $j_2^{\,p} =$ `A.valuation` $j_1$ then $s$ kills the class of $(x) - (\bar 0)$. Note that $T$ and $s$ are arbitrary, no finiteness being demanded of the target; all content lies in the three clauses.
--
--   This is the specialisation input for Step 3 of Mazur's Eisenstein-ideal argument (Mazur, Modular curves and the Eisenstein ideal, III §5, with the cusp description of Deligne–Rapoport and Raynaud's criterion for the $\ell$-part). Compared with the textbook statement, the formal version does not assert good reduction of the Eisenstein quotient or construct reduction modulo $\ell$ as a map of group schemes; it only asserts the existence of some additive map out of the Eisenstein quotient that is injective on the prime-to-$\ell$ rational torsion, injective on the $\ell$-part when $\ell \neq 2$, and satisfies the cusp rule, and it carries no guard excluding the small primes $p$ for which the quotient vanishes. It is one of the instantiations of the inputs in `ModularCurve_MazurStepThreeInputs` at the divisorial Hecke action `heckeModuleBar p`, and it is used in the proof of [`WeierstrassCurve.mazurStepThree_not_inZeroComponentAt`](thm.html#WeierstrassCurve.mazurStepThree_not_inZeroComponentAt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_mazurQuotientSpecialization_heckeModuleBar.lean

import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Definitions.Def_ModularCurve_HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.mazurQuotientSpecialization_heckeModuleBar (p : ℕ) [Fact p.Prime]
    (hcomm : HeckeOperatorsCommuteBar p) :
    MazurQuotientSpecialization p (heckeModuleBar p) := by sorry
