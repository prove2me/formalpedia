-- Prove2me | Theorems.Thm_MasulloRepair_log_window_measure_transport
-- name    : MasulloRepair.log_window_measure_transport
-- status  : Proved
-- author  : @ibecca
-- created : 2026-11-21T15:02:10.510342+00:00
-- url     : https://prove2.me/theorems/26e67703-1ee0-42bb-a7db-3b79a27940b9
-- title:
--   Exact logarithmic transport of compact-window L2 norms
-- statement:
--   For $a,s\in\mathbf R$ and $n\in\mathbf N$, let $\nu_{a,s,n}$ be the previously defined positive-axis window measure,
--   $$d\nu_{a,s,n}(t)=
--   1_{(0,\infty)}(t)\max\{t^{2a},t^{2(a+n)}\}(1+\log^2t)^{s/2}\,\frac{dt}{t},$$
--   and put
--   $$d\lambda_{a,s,n}(x)=
--   \max\{e^{2ax},e^{2(a+n)x}\}(1+x^2)^{s/2}\,dx.$$
--   The exponential map preserves these measures:
--   $$(\exp)_*\lambda_{a,s,n}=\nu_{a,s,n}.$$
--   For every complex-valued function $f$ on $\mathbf R$,
--   $$f\in L^2(\nu_{a,s,n})\ \Longleftrightarrow\
--   f\circ\exp\in L^2(\lambda_{a,s,n}),\qquad
--   \|f\|_{L^2(\nu_{a,s,n})}
--   =\|f\circ\exp\|_{L^2(\lambda_{a,s,n})}.$$
--
--   The norm equality is an equality of extended-valued seminorms, so it also records infinite norms. This supplies the exact bridge between the existing source-integral model and the logarithmic coordinates used for smooth approximation. All real $s$ are allowed, including every $s\ge0$ in the manuscript.
-- source:
--   Auxiliary theorem for the compact-window repair of A. M. Masullo, The Music of the Primes, Definition 9.2.2.1 and Lemma 9.2.2.2(3), printed pp. 412-413, and Proposition 9.2.2.4, p. 414. Frozen source: https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf . This develops Yi's proposed compact-window replacement (mission comment a96ab6a0-9f70-4b3f-ab3e-8c7e38a823f2), after the accepted completeness theorem fea3483f-d6b8-43ba-95b4-3acb3895e88f. It is an explicitly stated repair, not a claim that the original uniform supremum is finite. The change-of-variables input is Mathlib MeasureTheory/Function/JacobianOneDim.lean, lintegral_image_eq_lintegral_abs_deriv_mul. The source measure is identified in the accepted theorem 48469d43-3cb2-41ea-8959-73f1a209fe25.

import Definitions.Def_MasulloRepair_LogWindows
import Theorems.Thm_MasulloRepair_compact_window_measure_and_norm_identification
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false
open MeasureTheory Set Filter Topology MasulloRepair
open scoped ENNReal

theorem MasulloRepair.log_window_measure_transport (a s : ℝ) (n : ℕ) :
    MeasurePreserving Real.exp (logWindowMeasure a s n)
      (windowMeasure (halflineBaseMeasure a s) n) ∧
    ∀ f : ℝ → ℂ,
      (MemLp f 2 (windowMeasure (halflineBaseMeasure a s) n) ↔
        MemLp (fun x => f (Real.exp x)) 2 (logWindowMeasure a s n)) ∧
      eLpNorm f 2 (windowMeasure (halflineBaseMeasure a s) n) =
        eLpNorm (fun x => f (Real.exp x)) 2 (logWindowMeasure a s n) := by sorry
