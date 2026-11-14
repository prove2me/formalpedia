-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_symmetric_compound_kernel_symmetric
-- name    : KSATSingleFlip.Connect.symmetric_compound_kernel_symmetric
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:53:23.375969+00:00
-- url     : https://prove2.me/theorems/3791e1ed-8e67-4ab6-b881-74002b7cb730
-- title:
--   Symmetrized compound Poisson kernel is symmetric
-- statement:
--   The distribution of X−X′ for two independent copies of any finite-intensity compound Poisson law is invariant under negation. This is the symmetry of the kernel Kν used in Definition 4.2.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, Definition 4.2, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Mathlib
open MeasureTheory KSATSingleFlip.Connect
set_option autoImplicit false

theorem KSATSingleFlip.Connect.symmetric_compound_kernel_symmetric (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Measure.map (fun z : ℝ => -z) (compoundPoisson μ ∗ Measure.map (fun z : ℝ => -z) (compoundPoisson μ)) =
      compoundPoisson μ ∗ Measure.map (fun z : ℝ => -z) (compoundPoisson μ) := by sorry
