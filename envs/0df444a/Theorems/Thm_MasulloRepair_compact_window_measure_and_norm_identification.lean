-- Prove2me | Theorems.Thm_MasulloRepair_compact_window_measure_and_norm_identification
-- name    : MasulloRepair.compact_window_measure_and_norm_identification
-- status  : Proved
-- author  : @ibecca
-- created : 2026-11-21T02:11:54.87207+00:00
-- url     : https://prove2.me/theorems/48469d43-3cb2-41ea-8959-73f1a209fe25
-- title:
--   The repaired space uses exactly the manuscript compact-window integrals
-- statement:
--   Let $a,s\in\mathbf R$ and $n\in\mathbf N$. On the positive real axis put
--   $$d\mu_{a,s}(t)=t^{2a}(1+\log^2t)^{s/2}\,\frac{dt}{t},\qquad
--   d\nu_n(t)=\max\{1,t^{2n}\}\,d\mu_{a,s}(t).$$
--   Then, as measures on $\mathbf R$ extended by zero off the positive axis,
--   $$d\nu_n(t)=1_{(0,\infty)}(t)\max\{t^{2a},t^{2(a+n)}\}
--                  (1+\log^2t)^{s/2}\,\frac{dt}{t}.$$
--   For every $f\in L^2(\nu_n;\mathbf C)$, the following positive-axis integrand is integrable and
--   $$\|f\|_{L^2(\nu_n)}=
--   \left(\int_0^\infty |f(t)|^2\max\{t^{2a},t^{2(a+n)}\}
--                  (1+\log^2t)^{s/2}\,\frac{dt}{t}\right)^{1/2}.$$
--
--   This identifies each coordinate norm of the complete replacement with the actual compact-window expression for $[a,a+n]$ in (9.2.2.3). It includes all degrees $s\ge0$ used in the source, and in fact holds for every real $s$. It is the bridge from the compatible-product construction to the intended weighted integral, rather than a new choice of norm.
--
--   **Formalization Note.** The theorem states equality of the measures, integrability of the displayed density, and equality of the norms. Representatives of $L^2$ classes are used only inside expressions invariant under the relevant almost-everywhere relation.
-- source:
--   Repair of A. M. Masullo, The Music of the Primes, Definition 9.2.2.1 and Lemma 9.2.2.2(3)(a), equations (9.2.2.3), (9.2.2.6)-(9.2.2.7), printed pp. 412-413, with relevance to the proposed space in Proposition 9.2.2.4, p. 414. Frozen draft: https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf . Yi identified the uniform-supremum finiteness defect and proposed compact-window seminorms in Prove2Me mission comment a96ab6a0-9f70-4b3f-ab3e-8c7e38a823f2 (mission 638f9b7f-e232-4624-ba08-5889465bb1e7). This contribution develops that replacement, following the accepted cofinal convergence criterion 2cf713aa-17bf-4fe0-9b9f-b73f1670aac5. It does not assert the original uniform-norm definition is valid on all of its stated tests. This is the direct measure and norm bridge for the replacement space. It specializes the source compact-window expression to the cofinal windows [a,a+n], with the density dt/t explicit.

import Definitions.Def_MasulloRepair_WindowL2

set_option autoImplicit false
open MeasureTheory Set Filter Topology MasulloRepair
open scoped ENNReal

theorem MasulloRepair.compact_window_measure_and_norm_identification (a s : ℝ) (n : ℕ) :
    windowMeasure (halflineBaseMeasure a s) n =
      (volume.restrict (Ioi (0 : ℝ))).withDensity
        (fun t => ENNReal.ofReal
          (max (t^(2*a)) (t^(2*(a+(n : ℝ)))) * (1+(Real.log t)^2)^(s/2) / t)) ∧
    ∀ f : Lp ℂ 2 (windowMeasure (halflineBaseMeasure a s) n),
      IntegrableOn (fun t : ℝ => ‖f t‖^2 * max (t^(2*a)) (t^(2*(a+(n : ℝ)))) *
        (1+(Real.log t)^2)^(s/2) / t) (Ioi 0) ∧
      ‖f‖ = Real.sqrt (∫ t in Ioi (0 : ℝ),
        ‖f t‖^2 * max (t^(2*a)) (t^(2*(a+(n : ℝ)))) * (1+(Real.log t)^2)^(s/2) / t) := by sorry
