-- Prove2me | Theorems.Thm_LinMatroidSecretary_Online_gp_supermodular
-- name    : LinMatroidSecretary.Online.gp_supermodular
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:16:42.424571+00:00
-- url     : https://prove2.me/theorems/af7c068f-9a0b-4430-9389-b4634eb7aa44
-- title:
--   §3 claim — g_p is supermodular on the lattice of subspaces
-- statement:
--   Fix the sample size $k\ge1$ and a set $X$ with $|X|=i>k$, together with a family $\mu=(\mu_{X-e})_{e\in X}$ in which every $\mu_{X-e}$ is a probability distribution on the subspaces of $\langle X-e\rangle$ satisfying the Dimension Invariant Inequality (1) (the standing hypotheses of §3). Let $p\in P=P(X,\mu)$. Then for all subspaces $L,H\le\langle X\rangle$,
--   $$g_p(L)+g_p(H)\le g_p(L\cap H)+g_p(L+H).$$
--
--   Supermodularity is what allows the uncrossing argument of Lemma 4.
--
--   Differences from the source:
--   - encoding: LP variables p(e, W) for e ∈ Y, W ∈ supp(µ_{Y−e}) → a function p on all pairs (e, W); only the values on those pairs are constrained or used; reason: the values off the LP variables enter no formula, so the instances are the same
--   - encoding: finite-dimensional vector spaces, subspaces, probability distributions and integer dimensions → vectors in Fin d → F, Submodule lattices, Finsupp distributions and real casts of finrank (including real subtraction in Δ); reason: every finite-dimensional represented instance has coordinates; over a finite field all subspaces form a finite set, so finite support loses no distributions, and casts preserve the exact dimensions
-- source:
--   Kristóf Bérczi, Shaddin Dughmi, Vasilis Livanos, Jose Soto, Victor Verdugo, The Strong Secretary Conjecture is True for Linear Matroids, STOC 2027 submission #608 (October 2026), §3, the claim after (6), PDF p. 13 (printed p. 11)

import Mathlib
import Definitions.Def_LinMatroidSecretary_Online_Setting
import Definitions.Def_LinMatroidSecretary_Online_DimensionLP

namespace LinMatroidSecretary.Online

/-- §3 claim (PDF p. 13, printed 11): under the standing hypotheses of §3, for every `p ∈ P`,
`g_p` is supermodular on the subspaces of `⟨X⟩`. -/
theorem gp_supermodular {F : Type*} [Field F] [Fintype F] {d : ℕ} {ι : Type*} [Fintype ι]
    [LinearOrder ι] (v : ι → Fin d → F) (X : Finset ι) (k : ℕ) (hk : 1 ≤ k) (hkX : k < X.card)
    (μ : ι → Dist F d) (hμ : StandingFamily v X k μ)
    (p : ι → Submodule F (Fin d → F) → ℝ) (hp : InP v X k μ p)
    (L H : Submodule F (Fin d → F)) (hL : L ≤ spanOf v X) (hH : H ≤ spanOf v X) :
    gp v X k μ p L + gp v X k μ p H ≤ gp v X k μ p (L ⊓ H) + gp v X k μ p (L ⊔ H) := by sorry

end LinMatroidSecretary.Online
