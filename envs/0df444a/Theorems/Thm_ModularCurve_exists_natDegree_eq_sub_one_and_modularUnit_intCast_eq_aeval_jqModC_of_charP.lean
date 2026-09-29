-- Prove2me | Theorems.Thm_ModularCurve_exists_natDegree_eq_sub_one_and_modularUnit_intCast_eq_aeval_jqModC_of_charP
-- name    : ModularCurve.exists_natDegree_eq_sub_one_and_modularUnit_intCast_eq_aeval_jqModC_of_charP
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/257eade5-42e6-54b9-826f-71db0ec4dd28
-- title:
--   Modular unit mod q is a degree q-1 polynomial in j
-- statement:
--   Let $k$ be a field of characteristic $q$ for a prime $q$. Work in the Laurent series field $k((\mathfrak q))$, realised as Hahn series over $\mathbb Z$, and write $\bar\Delta := \mathfrak q\cdot\prod_{n\ge 1}(1-\mathfrak q^{n})^{24}$ for the image in $k((\mathfrak q))$ of the power series [`ModularCurve.dedekindEtaUnit`](def/ModularCurve_X0.html#L127) $=$ `etaProd`$^{24}$ under coefficientwise reduction along $\mathbb Z\to k$, multiplied by the monomial $\mathfrak q$ (the Hahn series `single (1 : ℤ) 1`). Let [`ModularCurve.qExpand k q`](def/ModularCurve_X0.html#L25) be the ring endomorphism of $k((\mathfrak q))$ obtained by reindexing exponents through multiplication by $q$ on $\mathbb Z$, i.e. $\mathfrak q\mapsto\mathfrak q^{q}$, and let $\bar\jmath :=$ [`ModularCurve.jqModC k`](def/ModularCurve_JqCoeff.html#L15) be $\mathfrak q^{-1}$ times the reduction into $k$ of `jNum` $=$ `eisenstein4`$^3\cdot$`dedekindEtaUnitInv`, that is, the $\mathfrak q$-expansion of the $j$-invariant with coefficients read in $k$. The assertion is that there exists a polynomial $G$ over $k$ whose natural degree equals $q-1$ (truncated subtraction in $\mathbb N$) such that $\bar\Delta\cdot\bigl(\mathrm{qExpand}\,k\,q\,(\bar\Delta)\bigr)^{-1}=G(\bar\jmath)$, the right-hand side being the evaluation of $G$ at $\bar\jmath$ in the $k$-algebra $k((\mathfrak q))$.
--
--   This identifies the $\mathfrak q$-expansion of the level-$q$ modular unit $\Delta(\mathfrak q)/\Delta(\mathfrak q^{q})$, read in characteristic $q$, with a polynomial in $j$ of degree exactly $q-1$; the polynomial is, up to normalisation, the classical Deuring–Hasse polynomial whose roots are the supersingular $j$-invariants. It is used in the computations of orders of this modular unit at non-affine places of the modular curve and in the verification that the mod-$\ell$ diamond action fixes the associated series.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_natDegree_eq_sub_one_and_modularUnit_intCast_eq_aeval_jqModC_of_charP.lean

import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.exists_natDegree_eq_sub_one_and_modularUnit_intCast_eq_aeval_jqModC_of_charP
    (k : Type*) [Field k] (q : ℕ) [Fact q.Prime] [CharP k q] :
    ∃ G : Polynomial k, G.natDegree = q - 1 ∧
      HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ k
          (ModularCurve.dedekindEtaUnit.map (Int.castRingHom k)) *
        (ModularCurve.qExpand k q (HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ k
          (ModularCurve.dedekindEtaUnit.map (Int.castRingHom k))))⁻¹
        = Polynomial.aeval (ModularCurve.jqModC k) G := by sorry
