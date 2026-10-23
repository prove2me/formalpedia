-- Prove2me | Theorems.Thm_IntuitiveDPI_Smooth_lemma_A_1
-- name    : IntuitiveDPI.Smooth.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:15:11.473026+00:00
-- url     : https://prove2.me/theorems/bc900e39-b0fe-433c-97b7-699d2e454245
-- title:
--   Lemma A.1, p. 9 — purified distance does not increase under CP trace non-increasing maps
-- statement:
--   Let $\mathcal E(X)=\sum_j K_jXK_j^\dagger$ be a completely positive map given by a finite family of Kraus operators $K_j:\mathcal H\to\mathcal H'$ which is trace non-increasing, $\sum_jK_j^\dagger K_j\le\mathbb 1$. Let $\rho,\sigma$ be subnormalized states on $\mathcal H$ (positive semidefinite with trace at most $1$). Then the purified distance $P(\rho,\sigma)=\sqrt{1-\bar F(\rho,\sigma)^2}$, with $\bar F$ the generalized fidelity, satisfies
--   $$P(\mathcal E(\rho),\mathcal E(\sigma))\le P(\rho,\sigma).$$
--
--   This monotonicity is used twice in the paper: with $\mathcal E$ the partial trace over $C$ in Theorem 1, and with $\mathcal E(X)=\Pi X\Pi$ for a projector $\Pi$ in the chain rule, Lemma 5.1.
--
--   **Formalization Note** "Completely positive" is encoded by the Kraus form, which is how finite-dimensional CP maps are given; the map is `QAlgorithms.krausApply K`. The purified distance and the generalized fidelity are those of `Information100.P67`.
-- source:
--   Beaudry & Renner, An intuitive proof of the data processing inequality, arXiv:1107.0740v2, p. 9, Lemma A.1, (A.2)

import Mathlib
import Definitions.Def_IntuitiveDPI_Smooth_Basic

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P67
open QAlgorithms.Papers.Independent.Dependency50.P35 (marginalAB renyiEntropy)
open scoped ComplexOrder Matrix
open Filter Topology

namespace IntuitiveDPI.Smooth

/-- Lemma A.1, (A.2), p. 9: the purified distance does not increase under a completely
positive trace non-increasing map `E(ρ) = Σ_j K_j ρ K_j†` with `Σ_j K_j† K_j ≤ 1`, for
subnormalized `ρ, σ`. -/
theorem lemma_A_1 {J ι κ : Type*} [Fintype J] [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (K : J → Matrix κ ι ℂ) (hK : IsTraceNonincreasingKraus K)
    (ρ σ : Matrix ι ι ℂ) (hρ : IsSubnormalized ρ) (hσ : IsSubnormalized σ) :
    purifiedDistance (krausApply K ρ) (krausApply K σ) ≤ purifiedDistance ρ σ := by sorry

end IntuitiveDPI.Smooth
