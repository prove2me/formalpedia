-- Prove2me | Theorems.Thm_ModularCurve_coeff_qExpansionDiffAlong_cartier_pow
-- name    : ModularCurve.coeff_qExpansionDiffAlong_cartier_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/5ada231e-2403-51d0-9216-594372b18434
-- title:
--   Cartier laws force aₙ(Cω)ᵖ=aₙₚ(ω) on q-expansions
-- statement:
--   Let $K$ be a perfect field of characteristic $p$ with $p$ prime, let $N \ge 1$, and let $F =$ `modularFunctionFieldC K N` be the intermediate field of the Laurent series field $K((q))$ generated over $K$ by the two series `jqModC K` (the series $q^{-1}$ times the reduction of the $j$-numerator power series) and `jqNModC K N` (its substitution $q \mapsto q^N$); assume `IsCurveOver K F`, i.e. every nonzero element of $F$ has a degree-zero principal divisor, every place of $F$ over $K$ has residue field finite over $K$, and $\Omega_{F/K}$ is free of rank one over $F$. Let $C \colon \Omega_{F/K} \to \Omega_{F/K}$ be an additive map satisfying the three Cartier laws: $C(f^p \cdot \omega) = f \cdot C\omega$, $C(\mathrm{d}f) = 0$ and $C(f^{p-1} \cdot \mathrm{d}f) = \mathrm{d}f$ for all $f \in F$ and $\omega \in \Omega_{F/K}$. Write $\varphi =$ `qExpansionDiffAlong` for the chosen $K$-linear map $\Omega_{F/K} \to K((q))$ along the inclusion $F \hookrightarrow K((q))$ sending $\mathrm{d}x$ to $\theta x$ and satisfying $\varphi(f \cdot \omega) = f\,\varphi(\omega)$ (and $0$ if no such map exists). Then for every $\omega \in \Omega_{F/K}$ and every $n \in \mathbb{Z}$, the $n$-th coefficient of $\varphi(C\omega)$, raised to the $p$-th power, equals the $np$-th coefficient of $\varphi(\omega)$.
--
--   This is the classical description of the Cartier operator on $q$-expansions, $C\left(\sum a_n q^n \frac{\mathrm{d}q}{q}\right) = \sum a_{np}^{1/p} q^n \frac{\mathrm{d}q}{q}$, stated for an arbitrary additive operator obeying the three Cartier laws on the characteristic-$p$ modular function field of level $N$; equivalently, $C$ followed by the coefficientwise Frobenius acts as $a_n \mapsto a_{np}$. It is used to identify the Cartier operator with the Hecke operator $U$ on $q$-expansions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coeff_qExpansionDiffAlong_cartier_pow.lean

import Mathlib
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open ModularCurve
open AlgebraicCurve

theorem ModularCurve.coeff_qExpansionDiffAlong_cartier_pow
    (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectField K]
    (N : ℕ) [NeZero N] [IsCurveOver K (modularFunctionFieldC K N)]
    (C : Ω[↥(modularFunctionFieldC K N)⁄K] →+ Ω[↥(modularFunctionFieldC K N)⁄K])
    (hsemi : ∀ (f : modularFunctionFieldC K N) (ω : Ω[↥(modularFunctionFieldC K N)⁄K]),
      C (f ^ p • ω) = f • C ω)
    (hker : ∀ f : modularFunctionFieldC K N,
      C (KaehlerDifferential.D K (modularFunctionFieldC K N) f) = 0)
    (hlog : ∀ f : modularFunctionFieldC K N,
      C (f ^ (p - 1) • KaehlerDifferential.D K (modularFunctionFieldC K N) f)
        = KaehlerDifferential.D K (modularFunctionFieldC K N) f)
    (ω : Ω[↥(modularFunctionFieldC K N)⁄K]) (n : ℤ) :
    (qExpansionDiffAlong (modularFunctionFieldC K N).val (C ω)).coeff n ^ p
      = (qExpansionDiffAlong (modularFunctionFieldC K N).val ω).coeff (n * p) := by sorry
