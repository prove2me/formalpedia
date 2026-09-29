-- Prove2me | Theorems.Thm_ModularCurve_qExpansionDiffAlong_cartier_eq_coeffMap_frobeniusEquiv_symm_heckeU
-- name    : ModularCurve.qExpansionDiffAlong_cartier_eq_coeffMap_frobeniusEquiv_symm_heckeU
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/5e66a3f9-1696-5d52-a9f6-b590db897ba2
-- title:
--   Cartier operator on q-expansions equals Uₚ twisted by σ⁻¹
-- statement:
--   Let $K$ be a perfect field of characteristic a prime $p$, let $N \ge 1$, and let $F_N = \mathrm{modularFunctionFieldC}\,K\,N$ be the intermediate field of the Laurent series field $K(\!(q)\!)$ obtained by adjoining to $K$ the two series `jqModC K` and `jqNModC K N` (the reduction of the $q$-expansion of $j$ and of its $N$-fold $q$-expansion rescaling). Assume $F_N$ is a curve over $K$ in the sense of `IsCurveOver`, i.e. every place of $F_N$ over $K$ has finite residue extension over $K$, principal divisors of degree zero exist for all nonzero elements, and $\Omega_{F_N/K}$ is free of rank one over $F_N$. Let $C \colon \Omega_{F_N/K} \to \Omega_{F_N/K}$ be additive and satisfy the three Cartier laws: $C(f^p \cdot \omega) = f\cdot C\omega$, $C(\mathrm{d}f) = 0$, and $C(f^{p-1}\,\mathrm{d}f) = \mathrm{d}f$ for all $f \in F_N$ and all $\omega$. Write $\mathrm{qexp}$ for `qExpansionDiffAlong` along the inclusion $F_N \hookrightarrow K(\!(q)\!)$, the chosen $K$-linear map $\Omega_{F_N/K} \to K(\!(q)\!)$ sending $\mathrm{d}f$ to $\theta(f)$ and satisfying $\mathrm{qexp}(f\cdot\omega) = f\,\mathrm{qexp}(\omega)$ (and $0$ if no such map exists). Then for every $\omega \in \Omega_{F_N/K}$, $\mathrm{qexp}(C\omega)$ equals the series obtained from $\mathrm{qexp}(\omega)$ by first applying the $U_p$-operator [`LaurentSeries.heckeU`](def/LaurentSeries_HeckeU.html#L22), whose $n$-th coefficient is the $(pn)$-th coefficient of the input, and then applying the inverse $\sigma^{-1}$ of the Frobenius automorphism of $K$ coefficientwise.
--
--   This is the operator form of the statement that the Cartier operator acts on mod-$p$ $q$-expansions as the Hecke operator $U_p$ composed with the inverse Frobenius twist on coefficients. It is used in the step showing that the part of the differentials cut out on $q$-expansions by $\mathbb{F}_p$-polynomial conditions in $U_p$ and the $T_\ell$ is stable under $C$, via [`ModularCurve.pullbackAlong_apply_mem_mTorsionDiffOf_of_mem_heckeTorsion_jZero_of_coe_eq_reductionModL`](thm.html#ModularCurve.pullbackAlong_apply_mem_mTorsionDiffOf_of_mem_heckeTorsion_jZero_of_coe_eq_reductionModL).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_qExpansionDiffAlong_cartier_eq_coeffMap_frobeniusEquiv_symm_heckeU.lean

import Mathlib
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_LaurentSeries_HeckeU

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open ModularCurve AlgebraicCurve

theorem ModularCurve.qExpansionDiffAlong_cartier_eq_coeffMap_frobeniusEquiv_symm_heckeU
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
    (ω : Ω[↥(modularFunctionFieldC K N)⁄K]) :
    qExpansionDiffAlong (modularFunctionFieldC K N).val (C ω)
      = coeffMap ((frobeniusEquiv K p).symm : K ≃+* K).toRingHom
          (LaurentSeries.heckeU K p (Fact.out : p.Prime).pos
            (qExpansionDiffAlong (modularFunctionFieldC K N).val ω)) := by sorry
