-- Prove2me | Theorems.Thm_ModularCurve_ord_heckeMultiplier_eq_of_ord_neg_of_eq_smul_map
-- name    : ModularCurve.ord_heckeMultiplier_eq_of_ord_neg_of_eq_smul_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/cae24853-f8d4-5e99-a2c4-d7e19b6b3b50
-- title:
--   Order of the Hecke multiplier at a pole of α^*j
-- statement:
--   Let $k$ be a perfect field, let $N$ and $\ell$ be positive integers with $\ell$ prime and $\ell \nmid N$. Write $C =$ `modularFunctionFieldC k N`, the subfield of $k((q))$ generated over $k$ by $j(q)$ and $j(q^N)$, and $R =$ `charLDegeneracyRoof k N ℓ`, the subfield generated over $k$ by $j(q)$, $j(q^N)$, $j(q^{\ell})$ and $j(q^{N\ell})$; let $\alpha =$ `heckeAlphaC` be the inclusion $C \hookrightarrow R$ and $\beta =$ `heckeBetaC` the $k$-algebra map induced by $q \mapsto q^{\ell}$, and let $\bar\jmath =$ `jGeomGen k N` be the element $j(q)$ of $C$. Assume that both $C$ and $R$ are curves over $k$ in the sense of `IsCurveOver`, i.e. every nonzero function has a principal divisor of degree $0$ recording its orders, all residue fields of places are finite over $k$, and the module of Kähler differentials is free of rank one; assume further that for every place of $C$ and of $R$ the differential of a uniformiser spans the differentials. Let $h \in R$ satisfy $d(\beta\bar\jmath) = h \cdot \alpha^{*}(d\bar\jmath)$, where $R$ is regarded as a $C$-algebra along $\alpha$ and $\alpha^{*}$ is the induced map on differentials, and assume $d(\alpha\bar\jmath) \neq 0$ and $d(\beta\bar\jmath) \neq 0$. Let $y$ be a place of $R$ with $\operatorname{ord}_y(\alpha\bar\jmath) < 0$ and such that the absolute values of $\operatorname{ord}_y(\alpha\bar\jmath)$ and of $\operatorname{ord}_y(\beta\bar\jmath)$ are nonzero in $k$. Then $\operatorname{ord}_y h = \operatorname{ord}_y(\beta\bar\jmath) - \operatorname{ord}_y(\alpha\bar\jmath)$.
--
--   This is the cusp bookkeeping for the multiplier relating the two degeneracy maps on the $\ell$-degeneracy roof: at a pole of $\alpha\bar\jmath$ of order prime to the characteristic one has $\operatorname{ord}(df) = \operatorname{ord} f - 1$ for both $\alpha\bar\jmath$ and $\beta\bar\jmath$, and the two contributions subtract. It is used in the analysis of the geometric Hecke correspondence, where traces along $\beta$ of functions multiplied by powers of the multiplier are placed in Riemann–Roch spaces attached to a weight divisor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ord_heckeMultiplier_eq_of_ord_neg_of_eq_smul_map.lean

import Mathlib
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
open AlgebraicCurve ModularCurve KaehlerDifferential

theorem ModularCurve.ord_heckeMultiplier_eq_of_ord_neg_of_eq_smul_map
    (k : Type*) [Field k] [PerfectField k] (N ℓ : ℕ) [NeZero N] [NeZero ℓ] [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    [AlgebraicCurve.IsCurveOver k ↥(modularFunctionFieldC k N)] [AlgebraicCurve.IsCurveOver k ↥(charLDegeneracyRoof k N ℓ)]
    [∀ v : Place k ↥(modularFunctionFieldC k N), v.DCoordGenerates] [∀ w : Place k ↥(charLDegeneracyRoof k N ℓ), w.DCoordGenerates]
    (h : ↥(charLDegeneracyRoof k N ℓ))
    (hD : letI := AlgebraicCurve.algebraAlong (heckeAlphaC k N ℓ)
      haveI := AlgebraicCurve.isScalarTower_along (heckeAlphaC k N ℓ)
      KaehlerDifferential.D k ↥(charLDegeneracyRoof k N ℓ) (heckeBetaC k N ℓ (jGeomGen k N))
        = h • KaehlerDifferential.map k k ↥(modularFunctionFieldC k N) ↥(charLDegeneracyRoof k N ℓ)
            (KaehlerDifferential.D k ↥(modularFunctionFieldC k N) (jGeomGen k N)))
    (hDα : KaehlerDifferential.D k ↥(charLDegeneracyRoof k N ℓ) (heckeAlphaC k N ℓ (jGeomGen k N)) ≠ 0)
    (hDβ : KaehlerDifferential.D k ↥(charLDegeneracyRoof k N ℓ) (heckeBetaC k N ℓ (jGeomGen k N)) ≠ 0)
    (y : Place k ↥(charLDegeneracyRoof k N ℓ))
    (hyα : y.ord (heckeAlphaC k N ℓ (jGeomGen k N)) < 0)
    (htα : ((y.ord (heckeAlphaC k N ℓ (jGeomGen k N))).natAbs : k) ≠ 0)
    (htβ : ((y.ord (heckeBetaC k N ℓ (jGeomGen k N))).natAbs : k) ≠ 0) :
    y.ord h = y.ord (heckeBetaC k N ℓ (jGeomGen k N)) - y.ord (heckeAlphaC k N ℓ (jGeomGen k N)) := by sorry
