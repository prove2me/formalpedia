-- Prove2me | Theorems.Thm_NarrowDNF_HatamiCrossTerms_crossEnvelope_le_corrected
-- name    : NarrowDNF.HatamiCrossTerms.crossEnvelope_le_corrected
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:47:36.210717+00:00
-- url     : https://prove2.me/theorems/ee418661-5ad2-4c5d-9d3c-05da644c7f31
-- title:
--   Corrected Fourier cross-envelope estimate
-- statement:
--   Let $f$ be Boolean on a finite cube, $0<p\le1/2$, $\delta\ge0$, $\eta>0$, and $k\in\mathbb R$. Let $\mathcal A=\{S:|S|\le k,\ \|F_S\|_\infty>\eta\}$, and form $J$ using threshold masses $m_S=P_p(|F_S|\ge\eta)$. For $\widetilde F_S=E_p[F_S\mid\mathcal F_{J_S}]$, define the nonnegative envelope
--   $$\mathcal C=\sum_{\substack{S,R\in\mathcal A\\S\ne R}}\max\{0,E_p[\widetilde F_S\widetilde F_R]\}.$$
--   Then
--   $$\mathcal C\le2^{8k}\delta/\eta^2.$$
--   The cutoff is real, and no additional lower bound on $k$ is assumed.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/HatamiCrossTerms.lean#L300-L345

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_Adaptive
import Definitions.Def_NarrowDNF_Certificates
import Definitions.Def_NarrowDNF_CoordinateShift
import Definitions.Def_NarrowDNF_Fourier
import Definitions.Def_NarrowDNF_HatamiActivation
import Definitions.Def_NarrowDNF_HatamiCrossTerms
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_LoadTransport
import Definitions.Def_NarrowDNF_ProductMeasure
import Theorems.Thm_NarrowDNF_HatamiActivation_localMass_le_componentTailMass
import Theorems.Thm_NarrowDNF_HatamiActivation_sum_componentTailMass_le
import Theorems.Thm_NarrowDNF_HatamiCrossTerms_crossEnvelope_le_kernel_sum
import Theorems.Thm_NarrowDNF_HatamiCrossTerms_intersection_kernel_sum_le

namespace NarrowDNF
end NarrowDNF

namespace NarrowDNF.Activation
end NarrowDNF.Activation

namespace NarrowDNF.FiberShift
end NarrowDNF.FiberShift

namespace NarrowDNF.Fourier
end NarrowDNF.Fourier

namespace NarrowDNF.HatamiActivation
end NarrowDNF.HatamiActivation

namespace NarrowDNF.HatamiCrossTerms
end NarrowDNF.HatamiCrossTerms

namespace NarrowDNF.HatamiResidual
end NarrowDNF.HatamiResidual

namespace NarrowDNF.Influence
end NarrowDNF.Influence

namespace NarrowDNF.ProductMeasure
end NarrowDNF.ProductMeasure
noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.HatamiCrossTerms
open ProductMeasure HatamiResidual HatamiActivation
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem NarrowDNF.HatamiCrossTerms.crossEnvelope_le_corrected {p k δ η : ℝ}
    (hp0 : 0 < p) (hp : p ≤ 1/2) (hδ : 0 ≤ δ) (hη : 0 < η) (f : Cube ι → Bool) :
    crossEnvelope p (fourierActivation k p δ η (fun x => Influence.boolValue (f x)))
      (fun x => Influence.boolValue (f x))
      (significantSets p (fun x => Influence.boolValue (f x)) k η) ≤
        (2:ℝ)^(8*k) * δ / η^2 := by sorry
