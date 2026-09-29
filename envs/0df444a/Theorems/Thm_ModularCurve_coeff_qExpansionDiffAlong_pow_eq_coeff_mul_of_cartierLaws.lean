-- Prove2me | Theorems.Thm_ModularCurve_coeff_qExpansionDiffAlong_pow_eq_coeff_mul_of_cartierLaws
-- name    : ModularCurve.coeff_qExpansionDiffAlong_pow_eq_coeff_mul_of_cartierLaws
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/3724ddbc-f91e-5ea3-9951-2f9f9364cfab
-- title:
--   q-expansion law for an abstract Cartier operator
-- statement:
--   Let $K$ be a perfect field of characteristic $p$ ($p$ prime), and let $F$ be an intermediate field of the Laurent series field $K((q))$ over $K$ which is a curve over $K$ in the sense of the project's predicate [`AlgebraicCurve.IsCurveOver`](def/AlgebraicCurve_IsCurveOver.html#L15): every nonzero element of $F$ admits a divisor of degree $0$ recording its order at each place of $F/K$, every place has residue field finite-dimensional over $K$, and $\Omega_{F/K}$ is free of rank one over $F$. Assume further that $F$ is finite-dimensional over $K(x)$ for some element $x$ of $F$. Let $C : \Omega_{F/K} \to \Omega_{F/K}$ be an additive map satisfying Cartier's three laws: $C(f^p\,\omega) = f\,C(\omega)$ for all $f \in F$ and all $\omega$, $C(df) = 0$ for all $f \in F$, and $C(f^{p-1}\,df) = df$ for all $f \in F$. Write $\Theta$ for the $K$-linear map $\Omega_{F/K} \to K((q))$ attached to the inclusion $F \hookrightarrow K((q))$ by [`ModularCurve.qExpansionDiffAlong`](def/ModularCurve_QExpansionDiff.html#L42), namely a chosen map with $\Theta(df) = \theta(f)$ for $f \in F$ and $\Theta(f\,\omega) = f\,\Theta(\omega)$ (and the zero map if no such map exists). Then for every $\omega \in \Omega_{F/K}$ and every $n \in \mathbb{Z}$, the $n$-th coefficient of $\Theta(C\omega)$ raised to the power $p$ equals the $(np)$-th coefficient of $\Theta(\omega)$.
--
--   This is the $q$-expansion, or decimation, law for the Cartier operator in the form $\mathcal{C}(a\,q^{pm}\,dq/q) = a^{1/p}q^{m}\,dq/q$ and $\mathcal{C}(a\,q^{n}\,dq/q) = 0$ for $p \nmid n$, stated for an arbitrary intermediate field $F$ of $K((q))$ that is a curve over $K$ and for any additive operator obeying Cartier's three axioms. It feeds the analysis of residues and of regularity of Frobenius-pushed differentials at the places of $F$ over the $q$-expansion place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coeff_qExpansionDiffAlong_pow_eq_coeff_mul_of_cartierLaws.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_QExpansionDiff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem ModularCurve.coeff_qExpansionDiffAlong_pow_eq_coeff_mul_of_cartierLaws
    {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectField K]
    (F : IntermediateField K (LaurentSeries K)) [AlgebraicCurve.IsCurveOver K ↥F]
    (x : ↥F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set ↥F)) ↥F]
    (C : Ω[↥F⁄K] →+ Ω[↥F⁄K])
    (hC1 : ∀ (f : ↥F) (ω : Ω[↥F⁄K]), C (f ^ p • ω) = f • C ω)
    (hC2 : ∀ f : ↥F, C (KaehlerDifferential.D K ↥F f) = 0)
    (hC3 : ∀ f : ↥F, C (f ^ (p - 1) • KaehlerDifferential.D K ↥F f) = KaehlerDifferential.D K ↥F f)
    (ω : Ω[↥F⁄K]) (n : ℤ) :
    (ModularCurve.qExpansionDiffAlong F.val (C ω)).coeff n ^ p =
      (ModularCurve.qExpansionDiffAlong F.val ω).coeff (n * p) := by sorry
