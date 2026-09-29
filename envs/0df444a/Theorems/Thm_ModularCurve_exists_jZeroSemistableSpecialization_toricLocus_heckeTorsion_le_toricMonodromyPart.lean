-- Prove2me | Theorems.Thm_ModularCurve_exists_jZeroSemistableSpecialization_toricLocus_heckeTorsion_le_toricMonodromyPart
-- name    : ModularCurve.exists_jZeroSemistableSpecialization_toricLocus_heckeTorsion_le_toricMonodromyPart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/862519c2-b17d-5f31-ada4-bf4c2a8c4ea1
-- title:
--   Toric 𝔪-torsion of J₀(Nq) lies in monodromy part
-- statement:
--   Let $N\ge 1$ and let $q$ be a prime not dividing $N$. Let $A$ be a valuation subring of an algebraic closure of $\mathbb{Q}$ lying over $q$, in the sense that the image of $q$ is a non-unit of $A$. Equip $J_0(Nq)=$ `JZero (N * q)` and `JZero N`, the degree-zero divisor class groups of the modular function fields over the algebraic closure, with the Hecke module structures `heckeModuleBar` over $\mathbb{T} =$ `HeckeAlg` $= \mathbb{Z}[X_\ell : \ell \text{ prime}]$, and give the modular function field `modularFunctionFieldC` of level $N$ over the residue field $\kappa$ of $A$ its $\kappa$-algebra structure. The assertion is that there exist a $\mathbb{T}$-module structure on $\mathrm{Pic}^0$ of that function field over $\kappa$ and a semistable specialisation datum $D$ of type `JZeroSemistableSpecialization A N q hq` (a finite set of node pairs of places with rational residue fields, a semilinear Frobenius automorphism stabilising them and acting as $a \mapsto a^q$ on $\kappa$, widths, a component homomorphism `comp` and a specialisation homomorphism `sp` into the glued $\mathrm{Pic}^0$, both defined on the inertia invariants of $J_0(Nq)$ and compatible with Hecke operators and Frobenius) with the following property. Let $\mathfrak m \subset \mathbb{T}$ be maximal, not eventually Eisenstein (there is no finite set $S$ of primes with $X_\ell - (\ell+1) \in \mathfrak m$ for all $\ell \notin S$), and with the image of $q$ a unit in $\mathbb{T}/\mathfrak m$. Let $x \in J_0(Nq)$ be annihilated by every element of $\mathfrak m$ and satisfy $n x = 0$ for some $n > 0$ with $q \nmid n$. If $x$ is fixed by every element of the inertia subgroup $I_A$ of $A$ over $\mathbb{Q}$ inside the automorphism group of the algebraic closure, and if $D.\mathrm{comp}(x) = 0$ in the component group and the image of $D.\mathrm{sp}(x)$ under `toPic0Pair` vanishes in the product of the two $\mathrm{Pic}^0$'s, then $x$ lies in `toricMonodromyPart q` $(I_A)$, the $\mathbb{T}$-span of the elements $\sigma \cdot y - y$ with $\sigma \in I_A$ and $y \in J_0(Nq)$ killed by some positive integer coprime to $q$.
--
--   This is the cokernel half of Grothendieck's monodromy pairing for $J_0(Nq)$ at $q$, in the form used by Ribet: at a non-Eisenstein maximal Hecke ideal the component group contributes nothing, so the $\mathfrak m$-torsion specialising into the torus consists of monodromy differences. It feeds the toric dichotomy [`ModularCurve.toricDichotomy_toricMonodromyPart_jZero`](thm.html#ModularCurve.toricDichotomy_toricMonodromyPart_jZero) in the proof of Mazur's principle.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_jZeroSemistableSpecialization_toricLocus_heckeTorsion_le_toricMonodromyPart.lean

import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_MazurPrincipleCore
import Definitions.Def_ModularCurve_ToricMonodromyPart

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000

theorem ModularCurve.exists_jZeroSemistableSpecialization_toricLocus_heckeTorsion_le_toricMonodromyPart (N q : ℕ) [NeZero N] (hq : q.Prime)
    (hqN : ¬ q ∣ N) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    letI := ModularCurve.heckeModuleBar (N * q)
    letI := ModularCurve.heckeModuleBar N
    letI := ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∃ _ : Module ModularCurve.HeckeAlg
        (AlgebraicCurve.Pic0 (IsLocalRing.ResidueField ↥A)
          ↥(ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField ↥A) N)),
      ∃ D : ModularCurve.JZeroSemistableSpecialization A N q hq,
        ∀ 𝔪 : Ideal ModularCurve.HeckeAlg, 𝔪.IsMaximal → ¬ ModularCurve.IsEventuallyEisenstein 𝔪 →
          IsUnit ((q : ℕ) : ModularCurve.HeckeAlg ⧸ 𝔪) →
            ∀ x ∈ ModularCurve.heckeTorsion (ModularCurve.JZero (N * q)) 𝔪,
              ModularCurve.PrimeToTorsion q x →
                ∀ h : x ∈ ModularCurve.inertiaInvariants A (N * q), D.comp ⟨x, h⟩ = 0 →
                  AlgebraicCurve.GluedPic0.toPic0Pair D.nodes (D.sp ⟨x, h⟩) = 0 →
                    x ∈ ModularCurve.toricMonodromyPart (J := ModularCurve.JZero (N * q)) q
                      (A.inertiaSubgroupIn ℚ) := by sorry
