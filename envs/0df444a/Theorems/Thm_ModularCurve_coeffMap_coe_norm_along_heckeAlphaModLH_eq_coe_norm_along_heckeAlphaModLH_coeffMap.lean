-- Prove2me | Theorems.Thm_ModularCurve_coeffMap_coe_norm_along_heckeAlphaModLH_eq_coe_norm_along_heckeAlphaModLH_coeffMap
-- name    : ModularCurve.coeffMap_coe_norm_along_heckeAlphaModLH_eq_coe_norm_along_heckeAlphaModLH_coeffMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/45b957a0-e939-551c-99ec-82711cd5ff07
-- title:
--   Coefficient base change commutes with the degeneracy norm
-- statement:
--   Let $k$ and $K$ be fields and $j\colon k\to K$ a ring homomorphism; let $N,\ell$ be natural numbers with $\ell\neq 0$ and let $H\le(\mathbb Z/N)^{\times}$ be a subgroup. For a field $L$ and a subgroup $\Gamma\le\mathrm{SL}(2,\mathbb Z)$, write $\bar F_L(\Gamma)$ for `qExpFunctionFieldC`, the intermediate field of $\mathrm{LaurentSeries}\,L$ generated over $L$ by the quotients $\mathrm{intSeriesC}\,L\,p_f/\mathrm{intSeriesC}\,L\,p_g$ of the $L$-reductions of integral $q$-expansions of modular forms $f,g$ of some common weight for $\Gamma$ (with the denominator non-zero), and let $\Gamma_H(N)$ be the image in $\mathrm{SL}(2,\mathbb Z)$ of the preimage of $H$ under the character $\Gamma_0(N)\to(\mathbb Z/N)^{\times}$ given by the lower-right entry. Let $\alpha_L=$ `heckeAlphaModLH` be the $L$-algebra inclusion $\bar F_L(\Gamma_H(N))\hookrightarrow\bar F_L(\Gamma_H(N)\cap\Gamma_0(N\ell))$ coming from monotonicity of $\bar F_L$ in the group. Assume that, with the algebra structures obtained along $\alpha_k$ and $\alpha_K$, the larger field is a finite module over the smaller one both for $k$ and for $K$, and that the two corresponding ranks agree. Then for every $x\in\bar F_k(\Gamma_H(N)\cap\Gamma_0(N\ell))$, the coefficientwise map `coeffMap j` sends the Laurent series underlying $\mathrm{N}_{\alpha_k}(x)\in\bar F_k(\Gamma_H(N))$ to the Laurent series underlying $\mathrm{N}_{\alpha_K}(\mathrm{coeffMap}\,j\,x)$, where `coeffMap j x` is regarded as an element of $\bar F_K(\Gamma_H(N)\cap\Gamma_0(N\ell))$ and the norms are the algebra norms along $\alpha_k$ and $\alpha_K$.
--
--   This is the compatibility of the norm map attached to the first degeneracy embedding $X(\Gamma_H(N)\cap\Gamma_0(N\ell))\to X_H(N)$ with change of the field of coefficients of $q$-expansions. It is used in the analysis of reduced root functions on $X_H$ in characteristic $\ell$, where a norm computed over one coefficient field must be transported along a homomorphism of coefficient fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coeffMap_coe_norm_along_heckeAlphaModLH_eq_coe_norm_along_heckeAlphaModLH_coeffMap.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_QExpCoeffSemilinearAut
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve AlgebraicCurve
open scoped MatrixGroups

theorem ModularCurve.coeffMap_coe_norm_along_heckeAlphaModLH_eq_coe_norm_along_heckeAlphaModLH_coeffMap
    (k K : Type*) [Field k] [Field K] (j : k →+* K)
    (N : ℕ) (H : Subgroup (ZMod N)ˣ) (ℓ : ℕ) [NeZero ℓ]
    (hfink : FiniteAlong k (heckeAlphaModLH k N H ℓ)) (hfinK : FiniteAlong K (heckeAlphaModLH K N H ℓ))
    (hdeg : finrankAlong k (heckeAlphaModLH k N H ℓ) = finrankAlong K (heckeAlphaModLH K N H ℓ))
    (x : ↥(qExpFunctionFieldC k (CohCarrier.GammaH N H ⊓ CongruenceSubgroup.Gamma0 (N * ℓ)))) :
    coeffMap j (((letI := algebraAlong (heckeAlphaModLH k N H ℓ)
        Algebra.norm ↥(qExpFunctionFieldC k (CohCarrier.GammaH N H)) x) : ↥(qExpFunctionFieldC k (CohCarrier.GammaH N H))) : LaurentSeries k) =
      (((letI := algebraAlong (heckeAlphaModLH K N H ℓ)
        Algebra.norm ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H))
          (⟨coeffMap j (x : LaurentSeries k),
            coeffMap_mem_qExpFunctionFieldC_of_mem j (CohCarrier.GammaH N H ⊓ CongruenceSubgroup.Gamma0 (N * ℓ)) x.2⟩ :
            ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))))) :
          ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H))) : LaurentSeries K) := by sorry
