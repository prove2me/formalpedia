-- Prove2me | Theorems.Thm_JHolomorphic_integrable_smul_of_integrableOn_compact
-- name    : JHolomorphic.integrable_smul_of_integrableOn_compact
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T13:39:12.146167+00:00
-- url     : https://prove2.me/theorems/87f2990b-f61c-444f-89ed-7f4e015774a0
-- title:
--   A compactly supported continuous weight times a locally integrable map is integrable
-- statement:
--   Let $U\subseteq\mathbb{C}$, let $f:\mathbb{C}\to E$ be integrable on every compact subset of $U$, and let $g:\mathbb{C}\to\mathbb{R}$ be continuous on $U$ with compact support contained in $U$. Then $z\mapsto g(z)\,f(z)$ is integrable on $\mathbb{C}$.
--
--   **Formalization Note** $E$ is a real normed space; the support condition is `HasCompactSupport g` and `tsupport g ⊆ U`; continuity is `ContinuousOn g U`; integrability is with respect to Lebesgue measure on $\mathbb{C}$.
-- source:
--   Standard (weak derivatives and distribution theory).

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp

namespace JHolomorphic

open MeasureTheory Filter Topology
open scoped ContDiff

/-- A real function that is continuous on `U` and has compact support in `U`, times a map that is
integrable on every compact subset of `U`, is integrable on `ℂ`. -/
theorem integrable_smul_of_integrableOn_compact {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {U : Set ℂ} {f : ℂ → E} (hf : ∀ K ⊆ U, IsCompact K → IntegrableOn f K)
    {g : ℂ → ℝ} (hg : ContinuousOn g U) (hgc : HasCompactSupport g) (hgU : tsupport g ⊆ U) :
    Integrable (fun z => g z • f z) := by
  sorry

end JHolomorphic
