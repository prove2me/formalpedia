-- Prove2me | Theorems.Thm_ModularCurve_rationalRankTwoCyclotomic_family
-- name    : ModularCurve.rationalRankTwoCyclotomic_family
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/7a3332b8-0207-5ab9-ad3a-d61c94c48a00
-- title:
--   Rationalised Eichler–Shimura: VₚJ₀(M) free of rank two
-- statement:
--   For every natural number $M$ with $0 < M$ and every prime $p$, equip the degree-zero Picard group [`ModularCurve.JZero M`](def/ModularCurve_ArithmeticGalois.html#L115) of the modular function field of level $M$ over $\overline{\mathbb{Q}}$ with the Hecke action [`ModularCurve.heckeModuleBar M`](def/ModularCurve_HeckeModule.html#L82), the module structure of the polynomial ring [`ModularCurve.HeckeAlg`](def/HeckeGalois_EichlerShimura.html#L14) $= \mathbb{Z}[T_\ell : \ell \text{ prime}]$ defined by the ring homomorphism `heckeEvalBar` built from the divisorial Hecke operators when these commute pairwise, and by evaluation of all variables at $0$ otherwise. The conclusion is the predicate [`ModularCurve.RationalRankTwoCyclotomic M p`](def/ModularCurve_JZeroTateModule.html#L106), that is `RationalRankTwoCyclotomicOf` for the extension $\mathbb{Q} \subseteq \overline{\mathbb{Q}}$: there exists a basis $b$, indexed by `Fin 2`, of the rational Tate module [`ModularCurve.RationalTateModule p (JZero M)`](def/ModularCurve_JZeroTateModule.html#L45) over the coefficient ring [`ModularCurve.rationalHeckeAlgebra p (JZero M)`](def/ModularCurve_JZeroTateModule.html#L76), such that for every prime $\ell$ with $\ell \nmid Mp$, every valuation subring $A'$ of $\overline{\mathbb{Q}}$ lying over $\ell$, and every $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ that is a Frobenius at $A'$ above $\ell$, the $2\times 2$ coordinate determinant of `rationalGaloisRep p (JZero M)` at $\sigma$ in the basis $b$, namely $b.\mathrm{repr}(\sigma b_0)_0\,b.\mathrm{repr}(\sigma b_1)_1 - b.\mathrm{repr}(\sigma b_1)_0\,b.\mathrm{repr}(\sigma b_0)_1$, equals the image of $\ell$ in `rationalHeckeAlgebra p (JZero M)`.
--
--   This is the rational form of the Eichler–Shimura description of the Tate module of $J_0(M)$: freeness of rank two over the Hecke algebra after tensoring with $\mathbb{Q}_p$, together with the cyclotomic determinant $\det \mathrm{Frob}_\ell = \ell$ coming from the Weil pairing, uniformly in the level $M$ and with no genus, multiplicity-one or Gorenstein hypothesis (at genus zero it holds degenerately). It is the source of the two-dimensional $p$-adic Galois representations attached to newforms and eigenplanes, and is cited in the construction of the Frobenius trace and determinant relations for those representations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_rationalRankTwoCyclotomic_family.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_ModularCurve_HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.rationalRankTwoCyclotomic_family :
    ∀ (M p : ℕ) (hM : 0 < M) (hp : p.Prime),
      haveI : NeZero M := ⟨hM.ne'⟩
      haveI : Fact p.Prime := ⟨hp⟩
      letI := ModularCurve.heckeModuleBar M
      ModularCurve.RationalRankTwoCyclotomic M p := by sorry
