-- Prove2me | Theorems.Thm_ModularCurve_rationalRankTwoNebentypus_family
-- name    : ModularCurve.rationalRankTwoNebentypus_family
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/f20e895f-c089-5089-a947-828a1987a411
-- title:
--   Rank-two freeness of VₚJ₁(M) with nebentypus determinant
-- statement:
--   For every natural number $M$ with $0 < M$ and every prime $p$, the predicate [`ModularCurve.RationalRankTwoNebentypus M p`](def/ModularCurve_X1HeckeModule.html#L257) holds for the Hecke-module structure [`ModularCurve.heckeModuleOneBar M`](def/ModularCurve_X1HeckeModule.html#L129) on $J =$ [`ModularCurve.JOne M`](def/ModularCurve_X1.html#L186), the degree-zero divisor class group $\mathrm{Pic}^0$ of the function field `x1FunctionFieldBar M` of $X_1(M)$ over $\overline{\mathbb Q}$. Here `HeckeAlgOne` is the polynomial ring $\mathbb Z[X_i]$ with indeterminates indexed by $\mathrm{Primes} \sqcup \mathbb N$, and `heckeModuleOneBar M` lets it act on $J$ through the ring homomorphism `heckeEvalOneBar` into $\mathrm{End}_{\mathbb Z}(J)$ when the commutation hypothesis `HeckeDiamondCommuteBar M` holds (which it does, by [`ModularCurve.heckeDiamondCommuteBar`](thm.html#ModularCurve.heckeDiamondCommuteBar)), and by the degenerate homomorphism sending all indeterminates to $0$ otherwise. Unfolding `RationalRankTwoNebentypusOf` at $K = \mathbb Q$, $L = \overline{\mathbb Q}$: there is a basis $b = (b_0,b_1)$ indexed by `Fin 2` of the rational Tate module `RationalTateModule p J` over the algebra `rationalHeckeAlgebraOne p J` such that for every prime $\ell$ with $\ell \nmid Mp$, every valuation subring $A'$ of $\overline{\mathbb Q}$ lying over $\ell$ and every $\sigma \in \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ that is a Frobenius at $\ell$ for $A'$, writing $c_{ji}$ for the $i$-th coordinate of `rationalGaloisRep p J _ σ (b j)` in the basis $b$, one has $$\mathrm{rationalDiamondOne}\,p\,J\,\ell \cdot (c_{00}c_{11} - c_{10}c_{01}) = \ell$$ in `rationalHeckeAlgebraOne p J`.
--
--   This is the rational form of Eichler–Shimura freeness for $X_1(M)$: the $p$-adic Tate module of $J_1(M)$, tensored with $\mathbb Q_p$, is free of rank two over the rational Hecke–diamond algebra acting on it, and in such a basis an arithmetic Frobenius at $\ell \nmid Mp$ has determinant $\langle\ell\rangle^{-1}\ell$. It is the source of the Frobenius characteristic polynomials for the $p$-adic representations attached to eigenforms, and is cited by the statements producing the characteristic polynomial and inertia relations for those representations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_rationalRankTwoNebentypus_family.lean

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.rationalRankTwoNebentypus_family :
    ∀ (M p : ℕ) (hM : 0 < M) (hp : p.Prime),
      haveI : Fact p.Prime := ⟨hp⟩
      letI := ModularCurve.heckeModuleOneBar M
      ModularCurve.RationalRankTwoNebentypus M p := by sorry
