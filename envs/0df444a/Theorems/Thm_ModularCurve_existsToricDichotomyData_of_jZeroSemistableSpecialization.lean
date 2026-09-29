-- Prove2me | Theorems.Thm_ModularCurve_existsToricDichotomyData_of_jZeroSemistableSpecialization
-- name    : ModularCurve.existsToricDichotomyData_of_jZeroSemistableSpecialization
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/d01db60f-0933-59e7-b53a-61c9018edf5e
-- title:
--   Toric dichotomy data from a semistable specialisation at q
-- statement:
--   Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$, let $N \ge 1$ and let $q$ be a prime; let $S$ be a finite set of primes containing every prime divisor of $Nq$, and let $\varphi$ be a $\mathbb{Q}$-automorphism of $\overline{\mathbb{Q}}$ which is a Frobenius at $A$ for $q$, i.e. $\varphi$ lies in the decomposition subgroup of $A$ over $\mathbb{Q}$ and acts on the residue field of $A$ by $x \mapsto x^{q}$. Equip $\mathrm{JZero}\,(Nq)$ and $\mathrm{JZero}\,N$ with the Hecke-algebra module structures `heckeModuleBar` (the Hecke algebra being $\mathbb{Z}[X_\ell : \ell \text{ prime}]$), use the residue-field algebra structure on the level-$N$ function field $\mathrm{modularFunctionFieldC}\,(\mathrm{ResidueField}\,A)\,N$, and assume given a Hecke-algebra module structure on the degree-zero divisor class group $\mathrm{Pic}^{0}$ of that function field. Then for every semistable specialisation datum $D$ of type `JZeroSemistableSpecialization A N q hq` — a finite set of node pairs of places of the level-$N$ function field over the residue field with rational residue fields, a semilinear automorphism inducing $x \mapsto x^{q}$ on the base whose permutation of the nodes is an involution, node widths, and additive maps $D.\mathrm{comp}$ to the component group and $D.\mathrm{sp}$ to the glued degree-zero class group, defined on the inertia invariants of $\mathrm{JZero}\,(Nq)$ and compatible with Hecke operators, Frobenius and the level-$N$ comparison, the fields being summarised here — there exists a Hecke submodule $\mathcal{T} \subseteq \mathrm{JZero}\,(Nq)$ with the following properties. First, membership is explicit: $x \in \mathcal{T}$ if and only if $x$ is prime-to-$q$ torsion (some $n > 0$ with $q \nmid n$ kills $x$) and $x$ is fixed by every element of the inertia subgroup of $A$ over $\mathbb{Q}$, with $D.\mathrm{comp}\,x = 0$ and with the image of $D.\mathrm{sp}\,x$ under `toPic0Pair` zero in the product of the two $\mathrm{Pic}^{0}$'s. Second, $\varphi$ acts on $\mathcal{T}$ with $\varphi^{2}x = q^{2}x$. Third, the $q$-guarded toric dichotomy holds towards $\mathrm{JZero}\,N$: for every maximal ideal $\mathfrak{m}$ of the Hecke algebra that is not eventually Eisenstein and for which $q$ is a unit modulo $\mathfrak{m}$, every inertia-invariant $\mathfrak{m}$-torsion class of $\mathrm{JZero}\,(Nq)$ either lies in $\mathcal{T}$ or $\mathrm{JZero}\,N$ carries lower-level $\mathfrak{m}$-torsion relative to $S$. Fourth, $\varphi x = (q\,X_{q})\,x$ for all $x \in \mathcal{T}$.
--
--   This is the passage, in Ribet's approach to level lowering, from a Deligne–Rapoport style semistable specialisation of $J_0(Nq)$ at a place above $q$ to the toric dichotomy at level $N$, with the toric submodule exposed by an explicit membership criterion so that the Frobenius relations and the dichotomy can be used simultaneously at one and the same $\mathcal{T}$. It is invoked by [`ModularCurve.exists_toricDichotomyData_jZero`](thm.html#ModularCurve.exists_toricDichotomyData_jZero) and by the newform statements producing eigenplanes and torus lines in the Tate module of $J_0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_existsToricDichotomyData_of_jZeroSemistableSpecialization.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_ToricDichotomyData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.existsToricDichotomyData_of_jZeroSemistableSpecialization
    (A : ValuationSubring (AlgebraicClosure ℚ)) (N q : ℕ) [NeZero N] (hq : q.Prime)
    (S : Finset Nat.Primes) (hSbad : ∀ ℓ : Nat.Primes, (ℓ : ℕ) ∣ N * q → ℓ ∈ S)
    (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hφ : A.IsFrobeniusAt φ q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    letI := ModularCurve.heckeModuleBar (N * q)
    letI := ModularCurve.heckeModuleBar N
    letI := ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ [Module ModularCurve.HeckeAlg (AlgebraicCurve.Pic0 (IsLocalRing.ResidueField A)
        (ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField A) N))]
      (D : ModularCurve.JZeroSemistableSpecialization A N q hq),
      ∃ 𝒯 : Submodule ModularCurve.HeckeAlg (ModularCurve.JZero (N * q)),
        (∀ x : ModularCurve.JZero (N * q), x ∈ 𝒯 ↔
          ModularCurve.PrimeToTorsion q x ∧
          ∃ h : x ∈ ModularCurve.inertiaInvariants A (N * q),
            D.comp ⟨x, h⟩ = 0 ∧
            AlgebraicCurve.GluedPic0.toPic0Pair D.nodes (D.sp ⟨x, h⟩) = 0) ∧
        ModularCurve.ToricFrobeniusSq (q : ℕ) φ 𝒯 ∧
        ModularCurve.IsToricDichotomyQGuarded (q : ℕ) S (A.inertiaSubgroupIn ℚ) 𝒯
          (ModularCurve.JZero N) ∧
        ModularCurve.ToricFrobeniusHecke ⟨q, hq⟩ φ 𝒯 := by sorry
