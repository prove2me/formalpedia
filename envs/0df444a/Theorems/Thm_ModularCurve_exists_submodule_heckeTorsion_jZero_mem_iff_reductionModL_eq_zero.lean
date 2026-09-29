-- Prove2me | Theorems.Thm_ModularCurve_exists_submodule_heckeTorsion_jZero_mem_iff_reductionModL_eq_zero
-- name    : ModularCurve.exists_submodule_heckeTorsion_jZero_mem_iff_reductionModL_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/45d1b120-9967-57dd-8a0c-3a9ac08b4f78
-- title:
--   Kernel of reduction on 𝔪-torsion is a T/𝔪-subspace
-- statement:
--   Let $M\ge 1$ be a natural number and $p$ a prime with $p\nmid M$, let $\mathfrak m$ be a maximal ideal of the Hecke polynomial ring `HeckeAlg` $=\mathbb Z[X_\ell:\ell\text{ prime}]$ (the multivariate polynomial ring over $\mathbb Z$ on the primes), and let $A$ be a valuation subring of $\overline{\mathbb Q}$ lying over $p$ in the sense of `LiesOverPrime`, i.e. the image of $p$ in $\overline{\mathbb Q}$ is a non-unit of $A$. Give `JZero M`, the degree-zero part of the divisor class group of the modular function field of level $M$ base-changed to $\overline{\mathbb Q}$, the `HeckeAlg`-module structure `heckeModuleBar M` (evaluation of polynomials at the divisorial Hecke operators `heckeOperatorBar M ℓ` when these commute, and the structure coming from evaluation at $0$ otherwise). The assertion is that there exists a submodule $K$ over the residue ring `HeckeAlg ⧸ 𝔪` of the $\mathfrak m$-torsion submodule `heckeTorsion (JZero M) 𝔪` $=$ `Submodule.torsionBySet HeckeAlg (JZero M) ↑𝔪` such that for every $w$ in that torsion submodule, $w\in K$ if and only if `reductionModL A M` applied to the underlying class of $w$ vanishes, where `reductionModL A M` is reduction along the residue map of $A$ into `JZeroC (ResidueField A) M` (a map defined to be $0$ should the reduction inputs for $A$ at level $M$ fail). Equivalently: the kernel of reduction, intersected with the $\mathfrak m$-torsion, is stable under the Hecke action and hence a $\mathbb T/\mathfrak m$-subspace.
--
--   This is the Hecke-equivariance of reduction of divisor classes at a place of $\overline{\mathbb Q}$ above a prime of good reduction, packaged as the statement that the reduction kernel inside $J_0(M)(\overline{\mathbb Q})[\mathfrak m]$ is a vector space over the residue field $\mathbb T/\mathfrak m$. It feeds the bound on the dimension of $J_0(M)[\mathfrak m]$ used in level lowering, via [`ModularCurve.finrank_heckeTorsion_jZero_le_two_of_isAbsolutelyIrreducible_of_heckeGen_notMem`](thm.html#ModularCurve.finrank_heckeTorsion_jZero_le_two_of_isAbsolutelyIrreducible_of_heckeGen_notMem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_submodule_heckeTorsion_jZero_mem_iff_reductionModL_eq_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve in

theorem ModularCurve.exists_submodule_heckeTorsion_jZero_mem_iff_reductionModL_eq_zero (M : ℕ) [NeZero M] (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M)
    (𝔪 : Ideal HeckeAlg) [𝔪.IsMaximal]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    letI := heckeModuleBar M
    ∃ K : Submodule (HeckeAlg ⧸ 𝔪) ↥(heckeTorsion (JZero M) 𝔪),
      ∀ w : ↥(heckeTorsion (JZero M) 𝔪), w ∈ K ↔ reductionModL A M (w : JZero M) = 0 := by sorry
