-- Prove2me | Theorems.Thm_MasulloGRH_meromorphic_logDeriv_regular_part
-- name    : MasulloGRH.meromorphic_logDeriv_regular_part
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T19:52:26.308669+00:00
-- url     : https://prove2.me/theorems/5dae10ad-59eb-4f3b-b3e2-b47699b4c2b3
-- title:
--   Analytic regular part of the logarithmic derivative at every finite meromorphic order
-- statement:
--   Let $f:\mathbb C\to\mathbb C$ be meromorphic at $p$ with finite meromorphic order $n\in\mathbb Z$. Define, away from $p$,
--
--   $$R(z)=\frac{f'(z)}{f(z)}-\frac{n}{z-p}.$$
--
--   There is a function $g$ analytic at $p$ which agrees with $R$ on a punctured neighborhood of $p$. Moreover there are positive real numbers $\varepsilon,C$ such that
--
--   $$0<|z-p|<\varepsilon\quad\Longrightarrow\quad |R(z)|\le C.$$
--
--   For a simple pole, $n=-1$, the regularized expression is $f'(z)/f(z)+1/(z-p)$. Positive orders, zero order and higher-order poles are covered by the same statement.
--
--   **Formalization note.** The hypothesis is the actual Mathlib equality `meromorphicOrderAt f p = (n : WithTop ℤ)`, not an assumed Laurent expansion or assumed bounded remainder. The integer order excludes the identically zero germ. The derivative and quotient are Mathlib's actual `deriv f z / f z`. Equality with the analytic regular part is only asserted in the punctured neighborhood, and no value for the original quotient at the singular point is prescribed. The positive constants are existential; this theorem is local and does not assert a global Hecke bound.
-- source:
--   General complex-analytic principal-part cancellation lemma isolating the analytic extension used in A. M. Masullo, The Music of the Primes, frozen 20 November 2026 draft, Appendix B, proof of Theorem B.7.1.2, equation (B.7.1.16), printed p. 648: https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf#page=648 . The manuscript uses the simple-pole case; this statement covers every finite meromorphic order. It supplies a local ingredient for MasulloGRH.heckeLFunction_logDeriv_bound_in_zero_free_region (b0595c1b-d3fe-4ff8-9080-64b6ab613616), without asserting the remaining Hecke-specific hypotheses or global estimate. Formal proof uses only Mathlib.

import Mathlib

set_option autoImplicit false
open Filter Set
open scoped Topology

theorem MasulloGRH.meromorphic_logDeriv_regular_part
    (f : ℂ → ℂ) (p : ℂ) (n : ℤ)
    (hf : MeromorphicAt f p) (hn : meromorphicOrderAt f p = (n : WithTop ℤ)) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g p ∧
      ((fun z : ℂ => deriv f z / f z - (n : ℂ) / (z - p)) =ᶠ[𝓝[≠] p] g) ∧
      ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧
        ∀ z : ℂ, 0 < ‖z - p‖ → ‖z - p‖ < ε →
          ‖deriv f z / f z - (n : ℂ) / (z - p)‖ ≤ C := by sorry
