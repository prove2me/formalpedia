-- Prove2me | Theorems.Thm_ModularCurve_exists_jZeroSemistableSpecialization_monodromy_mem_toricLocus
-- name    : ModularCurve.exists_jZeroSemistableSpecialization_monodromy_mem_toricLocus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/301c80ec-8019-5836-b48c-377fd943867b
-- title:
--   Prime-to-q monodromy lies in the toric locus
-- statement:
--   Let $N\ge 1$ (nonzero), let $q$ be a prime with $q\nmid N$, and let $A$ be a valuation subring of $\overline{\mathbb Q}$ lying over $q$ in the sense that $q$ is a nonunit of $A$; $\mathbb{Q}$-rational Hecke module structures on $J_0(N q)$ and $J_0(N)$, here the degree-zero divisor class groups `JZero` of the modular function fields over $\overline{\mathbb Q}$, are fixed by `heckeModuleBar`, and the residue field of $A$ acts on the function field `modularFunctionFieldC` of level $N$ over it. The assertion is that there exist a module structure for `HeckeAlg` $=\mathrm{MvPolynomial}\ \mathrm{Nat.Primes}\ \mathbb Z$ on $\mathrm{Pic}^0$ of that function field over the residue field of $A$, and a semistable specialisation datum $D$ of type `JZeroSemistableSpecialization A N q hq` (nodes given by a finite set of pairs of places with rational residue fields, a semilinear automorphism acting on scalars by $a\mapsto a^q$ and stabilising the nodes involutively, node widths, a component homomorphism `comp` and a specialisation homomorphism `sp` into the glued $\mathrm{Pic}^0$, subject to the datum's Hecke- and Frobenius-compatibility clauses), such that for every $\sigma$ in the inertia subgroup of $A$ over $\mathbb Q$ (the image of the inertia subgroup inside the decomposition subgroup) and every $x\in J_0(Nq)$ annihilated by some positive integer prime to $q$, the element $\sigma\cdot x-x$ is inertia-invariant and satisfies both $D.\mathrm{comp}(\sigma x-x)=0$ and $\mathrm{toPic0Pair}(D.\mathrm{sp}(\sigma x-x))=0$, i.e. it lies in the toric locus of $D$.
--
--   This is the formal counterpart of Grothendieck's description of tame monodromy on a semistable abelian variety: inertia at $q$ acts unipotently of level two on prime-to-$q$ torsion of $J_0(Nq)$, so that $(\sigma-1)x$ lands in the inertia-fixed toric part of the special fibre — here expressed by vanishing of both the component map and the pull-back of the specialisation to the two copies of the level-$N$ curve. It feeds the computation of the square of Frobenius on the toric monodromy part, [`ModularCurve.toricFrobeniusSq_toricMonodromyPart_jZero`](thm.html#ModularCurve.toricFrobeniusSq_toricMonodromyPart_jZero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_jZeroSemistableSpecialization_monodromy_mem_toricLocus.lean

import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000

theorem ModularCurve.exists_jZeroSemistableSpecialization_monodromy_mem_toricLocus (N q : ℕ) [NeZero N] (hq : q.Prime)
    (hqN : ¬ q ∣ N) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    letI := ModularCurve.heckeModuleBar (N * q)
    letI := ModularCurve.heckeModuleBar N
    letI := ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∃ _ : Module ModularCurve.HeckeAlg
        (AlgebraicCurve.Pic0 (IsLocalRing.ResidueField ↥A)
          ↥(ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField ↥A) N)),
      ∃ D : ModularCurve.JZeroSemistableSpecialization A N q hq,
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x : ModularCurve.JZero (N * q),
          ModularCurve.PrimeToTorsion q x →
            ∃ h : σ • x - x ∈ ModularCurve.inertiaInvariants A (N * q),
              D.comp ⟨σ • x - x, h⟩ = 0 ∧
                AlgebraicCurve.GluedPic0.toPic0Pair D.nodes (D.sp ⟨σ • x - x, h⟩) = 0 := by sorry
