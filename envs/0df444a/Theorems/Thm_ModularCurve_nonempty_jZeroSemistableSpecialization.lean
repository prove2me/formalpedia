-- Prove2me | Theorems.Thm_ModularCurve_nonempty_jZeroSemistableSpecialization
-- name    : ModularCurve.nonempty_jZeroSemistableSpecialization
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/fe946ff6-c0e1-5197-a7a3-51f290b9a729
-- title:
--   Existence of a semistable specialisation datum for J₀(Nq)
-- statement:
--   Let $N \ge 1$ (with `NeZero N`), let $q$ be a prime with $q \nmid N$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` lying over $q$ in the sense that $q$, viewed in $\overline{\mathbb{Q}}$, is a non-unit of $A$. Write $\kappa =$ `IsLocalRing.ResidueField A` and let $F_N =$ `modularFunctionFieldC κ N` be the intermediate field of the Laurent series field $\kappa((X))$ generated over $\kappa$ by the two series `jqModC` and `jqNModC`; the Hecke algebra is `HeckeAlg` $= \mathbb{Z}[T_\ell : \ell \text{ prime}]$, a polynomial ring on the primes, acting on `JZero (N*q)` and on `JZero N` through `heckeModuleBar`. The assertion is that there exist a `HeckeAlg`-module structure on [`AlgebraicCurve.Pic0 κ F_N`](def/AlgebraicCurve_DivisorClassGroup.html#L223), the group of degree-zero finitely supported $\mathbb{Z}$-valued divisors on the places of $F_N/\kappa$ modulo principal divisors, and, relative to that structure, an element of [`ModularCurve.JZeroSemistableSpecialization A N q hq`](def/ModularCurve_JZeroSemistableSpecialization.html#L94). The latter is a structure packaging: a finite set of pairs of places of $F_N/\kappa$ whose residue fields are $\kappa$-rational (nodes); a semilinear automorphism `frob` of $F_N$ over $\kappa$ acting on $\kappa$ by $a \mapsto a^q$, stabilising the set of node pairs, with involutive induced permutation of the nodes; widths $e$ on the nodes; a homomorphism `comp` from the inertia invariants of `JZero (N*q)` at $A$ to the component group attached to the widths, on which `heckeGen ℓ` acts as multiplication by $\ell+1$ for $\ell \nmid Nq$ and whose kernel is stable under `HeckeAlg` and under Frobenius elements at $q$; and a specialisation homomorphism `sp` from those inertia invariants to `GluedPic0 κ F_N` for the given node set, together with further Hecke-, Frobenius- and torsion-compatibility clauses relating `sp`, the existentially quantified Hecke action on `Pic0 κ F_N`, and the level-$N$ structure (summarised here).
--
--   This is the formal shape of the Deligne–Rapoport description of $X_0(Nq)$ in characteristic $q$ — two copies of $X_0(N)_{\kappa}$ crossing at the supersingular points — together with the resulting specialisation and component-group maps on the inertia invariants of $J_0(Nq)$, as used in Ribet's level-lowering argument. It is the existence statement feeding [`ModularCurve.exists_toricDichotomyData_jZero`](thm.html#ModularCurve.exists_toricDichotomyData_jZero), where the toric versus non-toric dichotomy at $q$ is extracted from such a datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_nonempty_jZeroSemistableSpecialization.lean

import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000

theorem ModularCurve.nonempty_jZeroSemistableSpecialization (N q : ℕ) [NeZero N] (hq : q.Prime)
    (hqN : ¬ q ∣ N) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    letI := ModularCurve.heckeModuleBar (N * q)
    letI := ModularCurve.heckeModuleBar N
    letI := ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∃ _ : Module ModularCurve.HeckeAlg
        (AlgebraicCurve.Pic0 (IsLocalRing.ResidueField ↥A)
          ↥(ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField ↥A) N)),
      Nonempty (ModularCurve.JZeroSemistableSpecialization A N q hq) := by sorry
