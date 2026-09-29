-- Prove2me | Theorems.Thm_ModularCurve_JZeroGoodReductionSpecialization_torsBijFor_of_charP_of_not_dvd
-- name    : ModularCurve.JZeroGoodReductionSpecialization.torsBijFor_of_charP_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/d6280591-280b-5776-bfe3-509b573c16fc
-- title:
--   Specialization is surjective on q-primary torsion, q≠ℓ
-- statement:
--   Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$, let $\ell$ be a prime, let $N\geq 1$, assume the residue field $\kappa_A$ of $A$ has characteristic $\ell$ and that $\ell\nmid N$, and fix Hecke-algebra module structures (the Hecke algebra being the polynomial ring $\mathbb{Z}[T_p : p \text{ prime}]$) on $J_0(N)=\mathrm{Pic}^0$ of the base-changed modular function field over $\overline{\mathbb{Q}}$ and on $\mathrm{Pic}^0$ of the function field $\kappa_A(j,j_N)$ generated over $\kappa_A$ by the two $q$-expansion generators; here $\mathrm{Pic}^0$ of a field extension means the group of degree-zero divisors, i.e. finitely supported $\mathbb{Z}$-valued functions on the places, modulo the subgroup of principal divisors. Let $D$ be a good-reduction specialization datum at $A$ for residue characteristic $\ell$: an additive surjection $\mathrm{sp}$ from $J_0(N)$ to the special-fibre $\mathrm{Pic}^0$ together with an endomorphism $F$ of the latter, such that $\mathrm{sp}$ is Hecke-equivariant, kills the action of the inertia subgroup of $A$ over $\mathbb{Q}$, satisfies $\mathrm{sp}(\sigma x)=F(\mathrm{sp}\,x)$ for every $\sigma$ that is a Frobenius at $A$ for $\ell$, is injective on $q$-primary torsion for every prime $q\neq\ell$, and such that $F$ satisfies $F^2-T_\ell F+\ell=0$ pointwise. The conclusion is `TorsBijFor` for $\ell$ and $\mathrm{sp}$: for every prime $q\neq\ell$ and every special-fibre class $y$ annihilated by some power $q^n$, there is an $x\in J_0(N)$ annihilated by some power of $q$ with $\mathrm{sp}(x)=y$.
--
--   This is the surjectivity half of the statement that specialization at a place of good reduction is an isomorphism on torsion prime to the residue characteristic; combined with the injectivity built into the datum, it identifies the $q$-primary torsion of $J_0(N)$ with that of the special fibre for $q\neq\ell$. It is one of the properties verified in the construction of a good-reduction specialization datum satisfying the required predicates, [`ModularCurve.exists_jZeroGoodReductionSpecialization_doorPredicates`](thm.html#ModularCurve.exists_jZeroGoodReductionSpecialization_doorPredicates).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroGoodReductionSpecialization_torsBijFor_of_charP_of_not_dvd.lean

import Definitions.Def_ModularCurve_JZeroGoodReductionV2
import Definitions.Def_ModularCurve_StepThreeDoorPredicates

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve IsLocalRing

attribute [local instance] ModularCurve.instDecEqResidueFieldF3nrp
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCF3nrp

theorem ModularCurve.JZeroGoodReductionSpecialization.torsBijFor_of_charP_of_not_dvd
    {A : ValuationSubring (AlgebraicClosure ℚ)} {ℓ : ℕ} {hℓ : ℓ.Prime} {N : ℕ} [NeZero N]
    [CharP (ResidueField A) ℓ] (hℓN : ¬ ℓ ∣ N)
    [Module HeckeAlg (JZero N)]
    [Module HeckeAlg (Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N))]
    (D : JZeroGoodReductionSpecialization A ℓ hℓ N) :
    TorsBijFor ℓ D.sp := by sorry
