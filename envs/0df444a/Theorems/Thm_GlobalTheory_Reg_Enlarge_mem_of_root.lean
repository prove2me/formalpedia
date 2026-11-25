-- Prove2me | Theorems.Thm_GlobalTheory_Reg_Enlarge_mem_of_root
-- name    : GlobalTheory.Reg.Enlarge.mem_of_root
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:14:36.101965+00:00
-- url     : https://prove2.me/theorems/5ce9a57b-618a-4211-a612-b7e1b13be86f
-- title:
--   Enlarge: mem of root
-- statement:
--   The Enlarge construction uses the mem of root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegralFlagChartEnlargeContainingValue.lean#L97-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegralFlagChartEnlargeContainingValue.lean#L97-L129

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_ModelAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralFlagChartEnlargeContainingValue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open GlobalTheory GlobalTheory.Reg GlobalTheory.Reg.Enlarge
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain Polynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem GlobalTheory.Reg.Enlarge.mem_of_root {K Ω L : Type} [Field K] [Field Ω] [Algebra K Ω] [Field L] [Algebra K L] (A : Subalgebra K Ω)
    (Sb : Subring Ω) (hSA : ∀ x ∈ Sb, x ∈ A) (ψ : A →ₐ[K] L) (W : ValuationSubring L)
    (hW : ∀ x (hx : x ∈ Sb), ψ ⟨x, hSA x hx⟩ ∈ W) (q : Polynomial Ω) (hqm : q.Monic) (hqc : ∀ i, q.coeff i ∈ Sb)
    (t : Ω) (ht : t ∈ A) (h0 : q.eval t = 0) : ψ ⟨t, ht⟩ ∈ W := by sorry
