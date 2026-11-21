-- Prove2me | Theorems.Thm_MasulloGRH_finiteRank_sot_tendsto_traceNorm
-- name    : MasulloGRH.finiteRank_sot_tendsto_traceNorm
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T00:59:54.348173+00:00
-- url     : https://prove2.me/theorems/44dd2d85-2c82-4550-8ff7-ab2aaf271196
-- title:
--   Lemma C.3.4.4(5) — $P_i\to0$ strongly and $F$ finite rank imply $\|P_iF\|_{\mathrm{Tr}}\to0$
-- statement:
--   Let $H$ be a complex Hilbert space, $F$ a finite-rank operator on $H$, and $(P_i)_{i\in I}$ a net of bounded operators on $H$ converging **strongly** to zero: $P_iu\to0$ for every $u\in H$. Then $P_iF\to0$ in trace norm:
--   $$\|P_iF\|_{\mathrm{Tr}}\longrightarrow0 .$$
--
--   This is part (5) of Lemma C.3.4.4 of the draft. It is the finite-rank step in the proof that compositions of a nuclear operator with strongly convergent projectors converge in $\mathrm N(H)$ (Proposition C.3.5.1 and Corollary C.3.5.5).
--
--   **Formalization Note** The net is expressed by an arbitrary filter `l` on the index type, which covers nets and sequences alike. "Finite rank" means that the range of $F$ is finite-dimensional. `traceNorm` is $\|S\|_{\mathrm{Tr}}=\operatorname{Trace}|S|$ from `Def_MasulloGRH_HilbertNuclear` (Definition C.3.4.2(2) of the draft).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, Lemma C.3.4.4 part (5), pp. 698-699

import Definitions.Def_MasulloGRH_HilbertNuclear

set_option autoImplicit false

namespace MasulloGRH

theorem finiteRank_sot_tendsto_traceNorm {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (F : H →L[ℂ] H)
    (hF : FiniteDimensional ℂ (LinearMap.range (F : H →ₗ[ℂ] H)))
    {ι : Type*} (l : Filter ι) (P : ι → H →L[ℂ] H)
    (hP : ∀ u : H, Filter.Tendsto (fun i => P i u) l (nhds 0)) :
    Filter.Tendsto (fun i => traceNorm (P i ∘L F)) l (nhds 0) := by sorry

end MasulloGRH
