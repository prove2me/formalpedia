-- Prove2me | Theorems.Thm_ModularCurve_eisensteinQuotientInvariantsFiniteAt_heckeModuleBar
-- name    : ModularCurve.eisensteinQuotientInvariantsFiniteAt_heckeModuleBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/70b9786a-c25e-5495-adec-16d8a29ba1a1
-- title:
--   Finiteness of the Galois invariants of the Eisenstein quotient of J₀(p)
-- statement:
--   Let $p$ be a natural number carrying a `Fact` instance asserting that it is prime, and assume `hcomm : HeckeOperatorsCommuteBar p`, i.e. that for all primes $\ell,\ell'$ the operators `heckeOperatorBar p ℓ` and `heckeOperatorBar p ℓ'` commute as $\mathbb{Z}$-linear endomorphisms of `JZero p`; here `JZero p` is $\mathrm{Pic}^0$ of the base change to $\overline{\mathbb{Q}}$ of the full modular function field of level $p$, and `heckeOperatorBar p ℓ` is the $\mathbb{Z}$-linear map underlying the divisor correspondence `heckeOperatorAlong` attached to the two degeneracy maps at $\ell$ (it is the correspondence $\beta_*\alpha^!$ when the integrality, fundamental-identity, finiteness and norm-formula inputs hold, and $0$ otherwise). Under `hcomm`, the Hecke module `heckeModuleBar p` is the module structure on `JZero p` over `HeckeAlg = MvPolynomial Nat.Primes ℤ` in which the generator $X_\ell$ acts as `heckeOperatorBar p ℓ`. The conclusion `EisensteinQuotientInvariantsFiniteAt p (heckeModuleBar p)` asserts the following. Write $\mathfrak{I} =$ `eisensteinIdeal p` for the kernel of the $\mathbb{Z}$-algebra map `HeckeAlg` $\to\mathbb{Z}$ sending $X_\ell\mapsto 1$ for $\ell\mid p$ and $X_\ell\mapsto 1+\ell$ otherwise, and write $\gamma$ for `eisensteinKernel`, the ideal of those $t\in$ `HeckeAlg` for which there is $i\in\mathfrak{I}$ with $((1+i)t)\cdot x=0$ for every $x\in$ `JZero p`. Then the image, under the quotient map `JZero p` $\to$ `JZero p`$/\,\gamma\cdot$`JZero p`, of the set of $x$ satisfying $\sigma\cdot x - x\in\gamma\cdot$`JZero p` for every $\sigma\in\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ (the automorphisms of $\overline{\mathbb{Q}}$ over $\mathbb{Q}$, acting on $\mathrm{Pic}^0$ semilinearly through the coefficients) is a finite set.
--
--   This is Mazur's finiteness theorem for the group of rational points of the Eisenstein quotient of $J_0(p)$ (Modular curves and the Eisenstein ideal, Chapter III, §1, Corollary 1.2). The formal statement differs in shape from the textbook one: there is no quotient abelian variety and no Mordell–Weil group, only the finiteness of a set of classes in the divisor class group $\mathrm{Pic}^0$ of the geometric modular function field modulo $\gamma\cdot\mathrm{Pic}^0$, the Hecke algebra being realised as a polynomial ring on the set of primes and the Eisenstein ideal as the kernel of the Eisenstein eigensystem; the invariance condition is imposed only up to $\gamma\cdot\mathrm{Pic}^0$, and for small $p$ the assertion is vacuous. It serves as the global input to [`WeierstrassCurve.mazurStepThree_not_inZeroComponentAt`](thm.html#WeierstrassCurve.mazurStepThree_not_inZeroComponentAt), the statement that a rational point of prime order $p\notin\{2,3,5,7,13\}$ on an integral Weierstrass curve which lies off the identity component at $2$ and $3$ lies off it at every multiplicative prime $\ell\neq p$, which in turn feeds Mazur's Eisenstein-ideal argument for irreducibility of the mod-$p$ representation of the Frey curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_eisensteinQuotientInvariantsFiniteAt_heckeModuleBar.lean

import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_Eisenstein

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.eisensteinQuotientInvariantsFiniteAt_heckeModuleBar (p : ℕ) [Fact p.Prime]
    (hcomm : HeckeOperatorsCommuteBar p) :
    EisensteinQuotientInvariantsFiniteAt p (heckeModuleBar p) := by sorry
