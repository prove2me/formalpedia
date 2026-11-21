-- Prove2me | Theorems.Thm_MasulloGRH_nuclear_trace_hasSum_hilbertBasis
-- name    : MasulloGRH.nuclear_trace_hasSum_hilbertBasis
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T00:47:00.364371+00:00
-- url     : https://prove2.me/theorems/edf55f93-ccbe-48d2-b0cc-1ee9cc4c6e60
-- title:
--   Lemma C.3.4.1(1),(3) — the trace of a nuclear operator is the same in every orthonormal basis
-- statement:
--   Let $H$ be a complex Hilbert space, $T$ a nuclear (trace-class) operator on $H$, and $\Sigma=(\phi_i)_{i\in I}$ **any** orthonormal basis of $H$. Then
--
--   1. the diagonal entries are absolutely summable: $\sum_{i\in I}|\langle T\phi_i,\phi_i\rangle|<\infty$;
--   2. their sum is the trace of $T$:
--   $$\sum_{i\in I}\langle T\phi_i,\phi_i\rangle=\operatorname{Trace}(T).$$
--
--   In particular the absolutely convergent sum $\sum_{\phi\in\Sigma}\langle T\phi,\phi\rangle$ does not depend on the orthonormal basis $\Sigma$. These are parts (1) and (3) of Lemma C.3.4.1 of the draft; they are what makes Definition C.3.4.2(1) of the trace well-posed.
--
--   **Formalization Note** `operatorTrace T` is defined in `Def_MasulloGRH_HilbertNuclear` as $\sum_i\langle T\phi_i,\phi_i\rangle$ over one orthonormal basis chosen once and for all; the theorem says the same value is obtained from every Hilbert basis `b`, of any index type. Mathlib's inner product is conjugate-linear in its first argument, so `inner ℂ (b i) (T (b i))` is $\langle T\phi_i,\phi_i\rangle$ in the convention of the draft. Nuclearity is `IsNuclearOperator`: $Tu=\sum_m\langle u,x_m\rangle y_m$ with $\sum_m\|x_m\|\,\|y_m\|<\infty$.
--
--   Part (2) of Lemma C.3.4.1 as printed (independence of $\sum_{\phi\in\Sigma}|\langle T\phi,\phi\rangle|$ from $\Sigma$) is not included here: that quantity does depend on the basis.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, Lemma C.3.4.1 parts (1) and (3), p. 697 (the draft cites Conway, A Course in Operator Theory, Ch. 3, Prop. 18.9)

import Definitions.Def_MasulloGRH_HilbertNuclear

set_option autoImplicit false

namespace MasulloGRH

theorem nuclear_trace_hasSum_hilbertBasis {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H) (hT : IsNuclearOperator T)
    {ι : Type*} (b : HilbertBasis ι ℂ H) :
    Summable (fun i => ‖inner ℂ (b i) (T (b i))‖) ∧
      HasSum (fun i => inner ℂ (b i) (T (b i))) (operatorTrace T) := by sorry

end MasulloGRH
