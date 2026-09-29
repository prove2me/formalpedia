-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_chartRing_le_span_coeffEmb_chartAlg
-- name    : ModularCurve.IgusaScheme.chartRing_le_span_coeffEmb_chartAlg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/815f5b52-7944-5dbf-a12a-cf30a4030f7d
-- title:
--   Geometric chart rings spanned by the integral chart algebras
-- statement:
--   Fix a natural number $N \ne 0$ and a natural number $\ell$ (no primality is assumed). Write $F_N =$ `modularFunctionFieldFull N` for the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the divisor expansions of level $N$, and let $\bar F_N =$ `modularFunctionFieldBar N` be its base change `laurentBaseChange` to a subfield of $\overline{\mathbb{Q}}((q))$; the map `coeffEmb` applies $\mathbb{Q} \to \overline{\mathbb{Q}}$ to Laurent coefficients and carries $F_N$ into $\bar F_N$. Let $\bar j =$ `jBar N` be the image of the $q$-expansion $j(q)$ in $\bar F_N$, and $j \in F_N$ its counterpart. Put $\mathbb{Z}_{(\ell)} =$ [`GaloisRep.ratLocalizedAt ℓ`](def/GaloisRep_Flat.html#L8), and let `chartAlgFin N ℓ` (resp. `chartAlgInf N ℓ`) be the subalgebra of elements of $F_N$ integral over $\mathbb{Z}_{(\ell)}[j]$ (resp. over $\mathbb{Z}_{(\ell)}[j^{-1}]$). Dually, `CurveModel.chartRing` over $\overline{\mathbb{Q}}$ of $\{\bar j\}$ (resp. $\{\bar j^{-1}\}$) consists of the elements of $\bar F_N$ integral over $\overline{\mathbb{Q}}[\bar j]$ (resp. $\overline{\mathbb{Q}}[\bar j^{-1}]$). The assertion is the conjunction of two inclusions of $\overline{\mathbb{Q}}$-submodules of $\bar F_N$: each of these two chart rings is contained in the $\overline{\mathbb{Q}}$-linear span of the coefficientwise image of the corresponding chart algebra.
--
--   This is one direction of the comparison that forming the integral closure in the two standard charts ($j$ finite, $j$ infinite) of the Igusa model commutes with the base change $\mathbb{Z}_{(\ell)} \to \overline{\mathbb{Q}}$; the reverse inclusion is automatic. It is used by the statements identifying $\overline{\mathbb{Q}} \otimes_{\mathbb{Z}_{(\ell)}} \mathrm{chartAlg}$, and its residue-field analogue, with the chart rings of the geometric fibre of the Igusa scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_chartRing_le_span_coeffEmb_chartAlg.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_ReductionOfPointsAgreesModL
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_FibreModel
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_JacJ1_ChartAlgebra

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  ModularCurve AlgebraicCurve IsLocalRing ModularCurve.IgusaScheme
open ModularCurve.CharPModel

theorem ModularCurve.IgusaScheme.chartRing_le_span_coeffEmb_chartAlg
    (N : ℕ) [NeZero N] (ℓ : ℕ) :
    (AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ)
        ({jBar N} : Set (modularFunctionFieldBar N))).toSubmodule ≤
      Submodule.span (AlgebraicClosure ℚ) (Set.range fun b : chartAlgFin N ℓ =>
        (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (b : ↥(modularFunctionFieldFull N)).2⟩ : modularFunctionFieldBar N)) ∧
    (AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ)
        ({(jBar N)⁻¹} : Set (modularFunctionFieldBar N))).toSubmodule ≤
      Submodule.span (AlgebraicClosure ℚ) (Set.range fun b : chartAlgInf N ℓ =>
        (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (b : ↥(modularFunctionFieldFull N)).2⟩ : modularFunctionFieldBar N)) := by sorry
