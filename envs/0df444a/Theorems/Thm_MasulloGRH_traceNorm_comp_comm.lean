-- Prove2me | Theorems.Thm_MasulloGRH_traceNorm_comp_comm
-- name    : MasulloGRH.traceNorm_comp_comm
-- status  : Disproved
-- author  : @marozols
-- created : 2026-11-21T00:55:59.291278+00:00
-- url     : https://prove2.me/theorems/5e3d6ee2-5591-4779-a9af-8ccbb514ea88
-- title:
--   Lemma C.3.4.4(2), first relation of (C.3.4.3) as printed — $\|AT\|_{\mathrm{Tr}}=\|TA\|_{\mathrm{Tr}}$
-- statement:
--   This node records the first relation of display (C.3.4.3) in Lemma C.3.4.4(2) of the draft **exactly as printed**, so that it can be checked.
--
--   Let $H$ be a Hilbert space, $T$ a nuclear (trace-class) operator on $H$ and $A$ a bounded operator on $H$. Lemma C.3.4.4(2) states
--   $$\|AT\|_{\mathrm{Tr}}=\|TA\|_{\mathrm{Tr}}\le\|A\|\,\|T\|_{\mathrm{Tr}} .\tag{C.3.4.3}$$
--   The present statement is the equality on the left:
--   $$\|AT\|_{\mathrm{Tr}}=\|TA\|_{\mathrm{Tr}},$$
--   where $\|S\|_{\mathrm{Tr}}=\operatorname{Trace}|S|$ with $|S|=(S^*S)^{1/2}$ is the trace norm of Definition C.3.4.2(2).
--
--   The inequalities $\|AT\|_{\mathrm{Tr}}\le\|A\|\|T\|_{\mathrm{Tr}}$ and $\|TA\|_{\mathrm{Tr}}\le\|A\|\|T\|_{\mathrm{Tr}}$, and the identity $\operatorname{Trace}(AT)=\operatorname{Trace}(TA)$, are separate statements and are not part of this node.
--
--   **Formalization Note** The Hilbert space is taken in the lowest universe, which is enough to test the statement. `traceNorm`, `operatorAbs` and `IsNuclearOperator` are from `Def_MasulloGRH_HilbertNuclear`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, Lemma C.3.4.4 part (2), equation (C.3.4.3), p. 698

import Definitions.Def_MasulloGRH_HilbertNuclear

set_option autoImplicit false

namespace MasulloGRH

theorem traceNorm_comp_comm (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H) (hT : IsNuclearOperator T)
    (A : H →L[ℂ] H) :
    traceNorm (A ∘L T) = traceNorm (T ∘L A) := by sorry

end MasulloGRH
