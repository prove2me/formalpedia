-- Prove2me | Theorems.Thm_FourierRankQLB_lemma_3_7
-- name    : FourierRankQLB.lemma_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:45:52.752192+00:00
-- url     : https://prove2.me/theorems/c52de505-a94a-4f28-aabe-75d9a4842069
-- title:
--   Lemma 3.7 — endpoint eigenangle density
-- statement:
--   Let $n=2N$ with $N\ge1$. The expected eigenangle density $\rho$ is defined by $\mathbb E[\text{number of eigenangles in }J]=\int_J\rho(\theta)\,d\theta$ for every measurable $J\subseteq[0,\pi]$.
--
--   1. Under $\mu_{n,+}$ there are almost surely $N$ positive eigenangles, with expected density
--   $$
--   \rho^+_N(\theta)=\frac1\pi+\frac2\pi\sum_{j=1}^{N-1}\cos^2(j\theta)\le\frac n\pi .
--   $$
--   2. Under $\mu_{n,-}$ there is almost surely one forced eigenvalue $+1$ and one forced eigenvalue $-1$. The remaining $N-1$ positive eigenangles have expected density
--   $$
--   \rho^-_N(\theta)=\frac2\pi\sum_{j=1}^{N-1}\sin^2(j\theta)\le\frac n\pi .
--   $$
--   3. Consequently, the expected number of these angles in a measurable $J\subseteq[0,\pi]$ is at most $n|J|/\pi$.
--
--   The lemma says few eigenangles of a Haar-random $Q\in SO(n)$ lie near $\pi$. It supplies the positive-component bound of Lemma 4.7.
--
--   **Formalization Note** The paper cites this lemma from the Weyl integration formula and does not prove it. The density identities themselves are stated, not only the bound.
--
--   Differences from the source:
--
--   - encoding: $n=2N$ → hypothesis `1 ≤ N`; reason: $O(0)$ has no eigenangles, and the lemma is used for $d\ge2$
--   - reading: eigenangles represent the rotation pairs of nonreal eigenvalues, by an angle in $[0,\pi]$ → `eigenangles` counts nonreal pairs only, so angles lie in $(0,\pi)$; reason: the page defines them from the nonreal eigenvalues; a real eigenvalue $\pm1$ beyond the forced ones occurs on a Haar-null set, so no expectation changes
--   - reading: almost surely one forced eigenvalue $+1$ and one forced eigenvalue $-1$ → almost surely each of $\pm1$ has multiplicity exactly one; reason: the stronger reading, matching the $N-1$ remaining angles of the page
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Lemma 3.7, p.21

import Mathlib
import Definitions.Def_FourierRankQLB_angleCount
import Definitions.Def_FourierRankQLB_muPlus
import Definitions.Def_FourierRankQLB_muMinus
import Definitions.Def_FourierRankQLB_rhoPlus
import Definitions.Def_FourierRankQLB_rhoMinus

open MeasureTheory

namespace FourierRankQLB

/-- Lemma 3.7 (Endpoint eigenangle density), for `n = 2N`.

Under `μ_{n,+}` there are almost surely `N` positive eigenangles, with expected density `ρ⁺_N ≤ n/π`.
Under `μ_{n,-}` there is almost surely one forced eigenvalue `+1` and one forced eigenvalue `-1`, and
the `N - 1` positive eigenangles have expected density `ρ⁻_N ≤ n/π`. Consequently the expected number
of angles in a measurable `J ⊆ [0, π]` is at most `n|J|/π`.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Lemma 3.7, p. 21.

**Formalization Note.** A density is an identity for every measurable `J ⊆ [0, π]`, as in the paper's
definition of `ρ`. `angleCount` counts nonreal rotation pairs with multiplicity; see `eigenangles`.
`N ≥ 1` is the case the paper uses; `O(0)` has no eigenangles and `ρ⁺_0 = 1/π`. -/
theorem lemma_3_7 {N : ℕ} (hN : 1 ≤ N) :
    (∀ᵐ Q ∂muPlus (2 * N), angleCount Q (Set.Icc 0 Real.pi) = N) ∧
    (∀ J : Set ℝ, MeasurableSet J → J ⊆ Set.Icc 0 Real.pi →
      ∫ Q, (angleCount Q J : ℝ) ∂muPlus (2 * N) = ∫ θ in J, rhoPlus N θ) ∧
    (∀ θ ∈ Set.Icc 0 Real.pi, rhoPlus N θ ≤ (2 * N : ℕ) / Real.pi) ∧
    (∀ᵐ Q ∂muMinus (2 * N), (eigenvaluesC Q).count 1 = 1 ∧ (eigenvaluesC Q).count (-1) = 1) ∧
    (∀ᵐ Q ∂muMinus (2 * N), angleCount Q (Set.Icc 0 Real.pi) = N - 1) ∧
    (∀ J : Set ℝ, MeasurableSet J → J ⊆ Set.Icc 0 Real.pi →
      ∫ Q, (angleCount Q J : ℝ) ∂muMinus (2 * N) = ∫ θ in J, rhoMinus N θ) ∧
    (∀ θ ∈ Set.Icc 0 Real.pi, rhoMinus N θ ≤ (2 * N : ℕ) / Real.pi) ∧
    (∀ J : Set ℝ, MeasurableSet J → J ⊆ Set.Icc 0 Real.pi →
      ∫ Q, (angleCount Q J : ℝ) ∂muPlus (2 * N) ≤ (2 * N : ℕ) * volume.real J / Real.pi ∧
      ∫ Q, (angleCount Q J : ℝ) ∂muMinus (2 * N) ≤ (2 * N : ℕ) * volume.real J / Real.pi) := by sorry

end FourierRankQLB
