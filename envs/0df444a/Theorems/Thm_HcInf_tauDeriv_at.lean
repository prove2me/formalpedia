-- Prove2me | Theorems.Thm_HcInf_tauDeriv_at
-- name    : HcInf.tauDeriv_at
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:22:27.526534+00:00
-- url     : https://prove2.me/theorems/48988cfd-49a8-412c-b539-326ca02f6daa
-- title:
--   Hc Inf: tau Deriv at
-- statement:
--   The Hc Inf construction uses the tau Deriv at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/HasFDerivAtTauR.lean#L88-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/HasFDerivAtTauR.lean#L88-L133

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExHua
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_HasFDerivAtTauR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HcInf
open HcS.BasicNotions Matrix Filter Topology
attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
variable {P Q : ℕ}
local notation "Mat" => Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ

theorem HcInf.tauDeriv_at (h : UpqT P Q) (x : lieU P Q) (hx : x ∈ D0 P Q)
    (hn : IsUnit (nH h (x : Mat)).det) :
    ∃ f' : lieU P Q →L[ℝ] lieU P Q,
      (∀ Y : lieU P Q, ((f' Y : lieU P Q) : Mat) = chA h (x : Mat) * (Y : Mat) * chB h (x : Mat)) ∧
      HasFDerivAt (tauL h) f' x := by sorry
