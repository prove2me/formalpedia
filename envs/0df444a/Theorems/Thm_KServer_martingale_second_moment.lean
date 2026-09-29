-- Prove2me | Theorems.Thm_KServer_martingale_second_moment
-- name    : KServer.martingale_second_moment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-01T09:34:25.280572+00:00
-- url     : https://prove2.me/theorems/20d03069-e8c3-436c-9415-6f86febf8d06
-- title:
--   Orthogonality of martingale increments (finite discrete form)
-- statement:
--   For a finite discrete martingale difference sequence $X_0, \dots, X_{N-1}$ with conditional variances $v_j$ (in the atom-encoded filtration model `IsDiscreteMartingale`), the second moment of the final partial sum is the expected total conditional variance:
--
--   $$\mathbb{E}\bigl[S_N^2\bigr] \;=\; \mathbb{E}\Bigl[\sum_{j<N} v_j\Bigr].$$
--
--   ## Role
--
--   The orthogonality of martingale increments — cross terms $\mathbb{E}[S_j X_j]$ vanish because $S_j$ is measurable at time $j$. In the Bubeck–Coester–Rabani stage-2a analysis this identifies the second moment of the stopped left-right imbalance with the accumulated conditional variance, which the stopping rule pins to a prescribed window; it is one half of the elementary anti-concentration argument replacing Ibragimov's martingale Berry–Esseen inequality.
--
--   ## Formalization note
--
--   The proof is a finite induction with a fiberwise conditioning lemma: sums over $\Omega$ split over the atoms of $\mathrm{hist}_j$, where time-$j$-measurable factors are constant.
-- source:
--   Classical (orthogonality of martingale increments); finite discrete form for BCR STOC 2023, Section 4.2.

import Mathlib
import Definitions.Def_KServer_discrete_martingale

namespace KServer

theorem martingale_second_moment {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {P : Ω → ℝ} {N : ℕ} {hist : ℕ → Ω → ℕ} {X v : ℕ → Ω → ℝ}
    (H : IsDiscreteMartingale P N hist X v) :
    ∑ ω, P ω * (mgSum X N ω) ^ 2 = ∑ ω, P ω * (∑ j ∈ Finset.range N, v j ω) := by sorry

end KServer
