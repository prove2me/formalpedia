-- Prove2me | Theorems.Thm_MasulloGRH_compact_sot_tendsto_norm
-- name    : MasulloGRH.compact_sot_tendsto_norm
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T00:42:17.448322+00:00
-- url     : https://prove2.me/theorems/9b33ecfa-cd97-4213-9af1-2ee9b3c117dd
-- title:
--   Lemma C.3.4.3 — strong convergence times a compact operator converges in norm
-- statement:
--   Let $H$ be a complex Hilbert space, $A$ a compact operator on $H$, and $Q,Q_0,Q_1,\dots$ bounded operators on $H$ such that $Q_m\to Q$ in the **strong operator topology**, i.e. $Q_mu\to Qu$ in $H$ for every $u\in H$. Then
--   $$\|Q_mA-QA\|\longrightarrow0,$$
--   that is, $Q_mA\to QA$ in the operator-norm topology.
--
--   This is Lemma C.3.4.3 of the draft. It is the mechanism by which strong convergence of projectors is upgraded to norm (and later trace-norm) convergence after composition with a compact operator, as used in §C.3.5 for the convergence of traces of compressions.
--
--   **Formalization Note** Compactness of $A$ is Mathlib's `IsCompactOperator`: the image of some neighbourhood of $0$ is contained in a compact set. The conclusion is convergence in the norm topology of `H →L[ℂ] H`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, Lemma C.3.4.3, p. 698

import Mathlib

set_option autoImplicit false

namespace MasulloGRH

theorem compact_sot_tendsto_norm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A Q : H →L[ℂ] H) (hA : IsCompactOperator A) (Qm : ℕ → H →L[ℂ] H)
    (hQ : ∀ u : H, Filter.Tendsto (fun m => Qm m u) Filter.atTop (nhds (Q u))) :
    Filter.Tendsto (fun m => Qm m ∘L A) Filter.atTop (nhds (Q ∘L A)) := by sorry

end MasulloGRH
