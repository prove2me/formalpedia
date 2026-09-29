-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_finite_etale_quotient_span_aeval_chartAlgFin
-- name    : ModularCurve.XHDRModelAtP.exists_finite_etale_quotient_span_aeval_chartAlgFin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/4b059aa9-fbb3-56c3-acd3-772859c0f8c5
-- title:
--   Étale level sets of the modular unit on the j-finite chart
-- statement:
--   Fix a natural number $p$ that is prime and a non-zero natural number $M$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and assume $p \mid M$ but $p^2 \nmid M$, together with the hypothesis that every unit $u$ of $\mathbb{Z}/M$ whose image under reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ is trivial lies in $H$. Assume further that the Laurent series `jqModC ℚ` (namely $q^{-1}$ times the integral power series $j$-numerator) lies in `qExpFunctionFieldC ℚ ⊤`, the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the integral form ratios at full level, and fix a term $\mathfrak{X}$ of the structure `XHDRModelAtP p M H hpM hj`, which packages a proper flat integral normal two-chart model over the base ring `R p` at level `ΓM M H` together with a smooth proper model at the auxiliary level, a curve model over $\overline{\mathbb{Q}}$ matched to it with its Galois compatibility, and smoothness and geometric integrality of the generic fibre. Write $A$ for `chartAlgFin p (ΓM M H) hj`, the subalgebra of elements of `qExpFunctionFieldC ℚ (ΓM M H)` integral over `R p`-adjoin-$j$, i.e. the integral closure of the polynomial ring in $j$ over `R p`. Let $v \in A$ have $q$-expansion either `modularUnitSeries p` $= \Delta \cdot \Delta_p^{-1}$ or $p^{12}$ times its inverse. Then there exist a non-zero $\mathrm{avoid} \in (\mathbb{Z}/p)[X]$, a non-zero $c_0 \in \mathbb{Z}[X]$ and $K \in \mathbb{N}$ such that for every monic $g \in \mathbb{Z}[X]$ of degree at least $1$ whose reduction modulo $p$ is irreducible and coprime to $\mathrm{avoid}$, and with $g \nmid c_0$ in $\mathbb{Z}[X]$, the quotient $A/(g(v))$ is a finite `R p`-module, étale as an `R p`-algebra, free as an `R p`-module, and of rank between $1$ and $K \cdot \deg g$.
--
--   The statement produces, for all but finitely many irreducible monic level polynomials $g$, finite étale free covers of the base obtained by cutting the $j$-finite chart of the two-chart integral model at level $\Gamma_H(M)$ along $g$ applied to Ogg's modular unit $\Delta(\tau)/\Delta(p\tau)$ (or its $p^{12}$-normalised inverse). It is used by [`ModularCurve.XHDRModelAtP.exists_levelPolynomials_of_chartAlgFin`](thm.html#ModularCurve.XHDRModelAtP.exists_levelPolynomials_of_chartAlgFin), which extracts from it a supply of level polynomials with the required integrality and ramification behaviour.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_finite_etale_quotient_span_aeval_chartAlgFin.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_ModularUnit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve Polynomial AlgebraicGeometry.Polynomial
open ModularCurve.XHDRLevel
open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 400000 in

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.XHDRModelAtP.exists_finite_etale_quotient_span_aeval_chartAlgFin
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (v : ↥(chartAlgFin p (ΓM M H) hj))
    (hv : ((v : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = modularUnitSeries p ∨
      ((v : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = (p : LaurentSeries ℚ) ^ 12 * (modularUnitSeries p)⁻¹) :
    ∃ (avoid : (ZMod p)[X]) (_ : avoid ≠ 0) (c₀ : ℤ[X]) (_ : c₀ ≠ 0) (K : ℕ),
      ∀ g : ℤ[X], g.Monic → 1 ≤ g.natDegree → Irreducible (g.map (Int.castRingHom (ZMod p))) →
        IsCoprime (g.map (Int.castRingHom (ZMod p))) avoid → ¬ g ∣ c₀ →
          Module.Finite (R p) (↥(chartAlgFin p (ΓM M H) hj) ⧸ Ideal.span {Polynomial.aeval v g}) ∧
          Algebra.Etale (R p) (↥(chartAlgFin p (ΓM M H) hj) ⧸ Ideal.span {Polynomial.aeval v g}) ∧
          Module.Free (R p) (↥(chartAlgFin p (ΓM M H) hj) ⧸ Ideal.span {Polynomial.aeval v g}) ∧
          1 ≤ Module.finrank (R p) (↥(chartAlgFin p (ΓM M H) hj) ⧸ Ideal.span {Polynomial.aeval v g}) ∧
          Module.finrank (R p) (↥(chartAlgFin p (ΓM M H) hj) ⧸ Ideal.span {Polynomial.aeval v g}) ≤ K * g.natDegree := by sorry
