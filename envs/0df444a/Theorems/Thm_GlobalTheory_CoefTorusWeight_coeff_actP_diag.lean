-- Prove2me | Theorems.Thm_GlobalTheory_CoefTorusWeight_coeff_actP_diag
-- name    : GlobalTheory.CoefTorusWeight.coeff_actP_diag
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:15:36.87223+00:00
-- url     : https://prove2.me/theorems/b6ed31f1-f11e-421b-b284-82d520a802f4
-- title:
--   Coef Torus Weight: coeff act P diag
-- statement:
--   The Coef Torus Weight construction uses the coeff act P diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeylTensorCoefSpaceEndomorphismPreservesTorusWei.lean#L30-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeylTensorCoefSpaceEndomorphismPreservesTorusWei.lean#L30-L47

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeylTensorCoefSpaceEndomorphismPreservesTorusWei
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix
open GlobalTheory GlobalTheory.CoefTorusWeight

theorem GlobalTheory.CoefTorusWeight.coeff_actP_diag {K ι : Type} [Field K] [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (t : ι → Fin n → Kˣ) (F : Pol K ι n) (m : (ι × Fin n × Fin n) →₀ ℕ) :
    coeff m (actP lam (fun τ => diagGL K n (t τ)) F)
      = detTwK lam (fun τ => diagGL K n (t τ)) *
        ((∏ v : ι × Fin n × Fin n, (t v.1 v.2.1 : K) ^ m v) * coeff m F) := by sorry
