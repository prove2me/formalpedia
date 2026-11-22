-- Prove2me | Theorems.Thm_MasulloGRH_isNuclearOperator_comp_traceNorm_le
-- name    : MasulloGRH.isNuclearOperator_comp_traceNorm_le
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:23:25.939437+00:00
-- url     : https://prove2.me/theorems/4fdb62d1-d9fe-4460-abf8-227fe749f93a
-- title:
--   Lemma C.3.4.4(1),(2), corrected — $N(H)$ is a two-sided ideal and $\|AT\|_{\mathrm{Tr}},\ \|TA\|_{\mathrm{Tr}}\le\|A\|\,\|T\|_{\mathrm{Tr}}$
-- statement:
--   **The nuclear operators form a two-sided ideal, with the ideal inequality for the trace norm.**
--
--   Let $H$ be a complex Hilbert space. A bounded operator $T$ on $H$ is **nuclear** (trace class) if $Tu=\sum_m\langle u,x_m\rangle y_m$ for sequences with $\sum_m\|x_m\|\|y_m\|<\infty$; write $N(H)$ for the set of nuclear operators. The **trace norm** of $T\in N(H)$ is
--   $$\|T\|_{\mathrm{Tr}}=\operatorname{Trace}(|T|)=\sum_{\phi\in\Sigma}\langle|T|\phi,\phi\rangle_H,\qquad|T|=(T^*T)^{1/2},$$
--   for an orthonormal basis $\Sigma$ of $H$.
--
--   Let $T\in N(H)$ and let $A$ be a bounded operator on $H$, with operator norm $\|A\|$. Then $AT$ and $TA$ are nuclear, and
--   $$\|AT\|_{\mathrm{Tr}}\le\|A\|\,\|T\|_{\mathrm{Tr}},\qquad\|TA\|_{\mathrm{Tr}}\le\|A\|\,\|T\|_{\mathrm{Tr}} .$$
--
--   So $N(H)$ is a two-sided ideal of $\mathscr B(H)$ on which left and right multiplication by bounded operators is continuous for the trace norm; this is used throughout the convergence results of §C.3.5 (compositions of a nuclear operator with projectors).
--
--   **Deviation from the source.** The paper prints $\|AT\|_{\mathrm{Tr}}=\|TA\|_{\mathrm{Tr}}\le\|A\|\|T\|_{\mathrm{Tr}}$ in (C.3.4.3). The equality is false (on $\mathbb C^2$ take $A=\operatorname{diag}(1,0)$ and $Te_1=e_2$, $Te_2=0$: then $AT=0$ while $TA=T$ has trace norm $1$); the correct classical statement, given here, consists of the two upper bounds.
--
--   **Formalization Note.** `IsNuclearOperator` and `traceNorm` are from `Def_MasulloGRH_HilbertNuclear`; `traceNorm` is the real part of the sum of $\langle|T|\phi,\phi\rangle$ over one fixed orthonormal basis, which is the trace norm for nuclear operators.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 698, Lemma C.3.4.4(1),(2), (C.3.4.3) (corrected); classical reference: J. Conway, A Course in Operator Theory, AMS (the paper's [Cnw-c]), Ch. 3, Thm. 18.11(a),(g),(e)

import Mathlib
import Definitions.Def_MasulloGRH_HilbertNuclear

open Filter Topology MeasureTheory
set_option autoImplicit false

namespace MasulloGRH

theorem isNuclearOperator_comp_traceNorm_le {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (hT : IsNuclearOperator T) (A : H →L[ℂ] H) :
    IsNuclearOperator (A ∘L T) ∧ IsNuclearOperator (T ∘L A) ∧
      traceNorm (A ∘L T) ≤ ‖A‖ * traceNorm T ∧
      traceNorm (T ∘L A) ≤ ‖A‖ * traceNorm T := by sorry

end MasulloGRH
