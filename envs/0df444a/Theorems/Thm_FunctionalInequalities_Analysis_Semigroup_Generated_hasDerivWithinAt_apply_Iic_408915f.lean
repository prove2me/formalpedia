-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Semigroup_Generated_hasDerivWithinAt_apply_Iic_408915f
-- name    : FunctionalInequalities.Analysis.Semigroup.Generated.hasDerivWithinAt_apply_Iic_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:09:04.483714+00:00
-- url     : https://prove2.me/theorems/86f33cd9-148d-4107-a248-58a039d2dbad
-- title:
--   Left Semigroup Derivative on Positive Times
-- statement:
--   This is the left derivative formula for a generated semigroup orbit.
--
--   Let $H_0,H_1$ be complete real Hilbert spaces, let $T:H_0\to H_1$ be closed with dense domain, let $A=T^\dagger T$, and let $f\in D(A)$. For $t>0$, the function $s\mapsto P_s f$ has a derivative at $t$ from the set $(-\infty,t]$:
--
--   $$\frac{d}{ds}\Big|_{s=t^-}P_s f=-A(P_t f).$$
--
--   Formally, `HasDerivWithinAt` is taken on `Iic t`, and the derivative is represented using the domain witness that $P_t f\in D(A)$. This is a one-sided derivative statement, not an unrestricted derivative assertion.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Semigroup/Generated/TimeDerivative.lean#L77-L115 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Semigroup.Generated.TimeDerivative`, declaration `FunctionalInequalities.Analysis.Semigroup.Generated.hasDerivWithinAt_apply_Iic`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_AdjointClosure
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_AdjointComp
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_Contraction
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_Dissipation
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_Limit
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_MeanValue
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Domain
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_FormDomain
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Generator
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Laws
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Smoothing
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Resolvent_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Resolvent_Form
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Resolvent_Limit
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_VonNeumann
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Yosida_Approximation
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Yosida_Laws
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Yosida_Limit
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.Module.LinearPMap

noncomputable section
open Filter Topology Set
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.Semigroup
end FunctionalInequalities.Analysis.Semigroup
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.Semigroup
section
namespace FunctionalInequalities.Analysis.Semigroup.Generated
end FunctionalInequalities.Analysis.Semigroup.Generated
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.Semigroup.Generated
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))

theorem FunctionalInequalities.Analysis.Semigroup.Generated.hasDerivWithinAt_apply_Iic_408915f (f : (adjointComp T).domain) {t : ℝ} (ht : 0 < t) :
    HasDerivWithinAt (fun s => apply T hT hd s f)
      (-adjointComp T ⟨apply T hT hd t f, preserves_domain T hT hd f ht.le⟩) (Iic t) t := by sorry
