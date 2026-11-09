-- Prove2me | Theorems.Thm_LinMatroidSecretary_Online_lemma_1
-- name    : LinMatroidSecretary.Online.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:16:38.814351+00:00
-- url     : https://prove2.me/theorems/9f587f31-8249-45da-bea6-2c9e306d6bfd
-- title:
--   Lemma 1 — the expected-dimension identity for µ_Y
-- statement:
--   Let $k\ge1$ be the sample size and let $Y$ be a set of elements with $|Y|=i>k$. Suppose that for every $e\in Y$, $\mu_{Y-e}$ is a probability distribution supported on the subspaces of $\langle Y-e\rangle$, and let $p=(p(e,W): e\in Y,\ W\in\operatorname{supp}\mu_{Y-e})$ satisfy $p(e,W)\in[0,1]$. Define $\mu_Y$ by (2) and $g_p$ by (3). Then:
--
--   1. for every subspace $L$,
--   $$\mathbb E_{U\sim\mu_Y}[\dim(U\cap L)]=\frac1i\bigl((i-k)\dim L+g_p(L)\bigr);$$
--   2. for every subspace $L$, the Dimension Invariant Inequality for $L$ at size $i$, $\mathbb E_{U\sim\mu_Y}[\dim(U\cap L)]\le(1-k/i)\dim L$, holds if and only if $g_p(L)\le0$;
--   3. if $g_p(L)\le0$ for every $L\le\langle Y\rangle$, then $\mu_Y$ satisfies the Dimension Invariant Inequality (1) for every subspace $L$.
--
--   The lemma turns the requirement that the updated distribution keeps the invariant into the linear constraints $g_p(L)\le 0$ of $\mathrm{LP}(Y)$.
--
--   Differences from the source:
--   - encoding: LP variables p(e, W) for e ∈ Y, W ∈ supp(µ_{Y−e}) → a function p on all pairs (e, W); only the values on those pairs are constrained or used; reason: the values off the LP variables enter no formula, so the instances are the same
--   - encoding: finite-dimensional vector spaces, subspaces, probability distributions and integer dimensions → vectors in Fin d → F, Submodule lattices, Finsupp distributions and real casts of finrank (including real subtraction in Δ); reason: every finite-dimensional represented instance has coordinates; over a finite field all subspaces form a finite set, so finite support loses no distributions, and casts preserve the exact dimensions
-- source:
--   Kristóf Bérczi, Shaddin Dughmi, Vasilis Livanos, Jose Soto, Victor Verdugo, The Strong Secretary Conjecture is True for Linear Matroids, STOC 2027 submission #608 (October 2026), Lemma 1, PDF pp. 8–9 (printed pp. 6–7)

import Mathlib
import Definitions.Def_LinMatroidSecretary_Online_Setting
import Definitions.Def_LinMatroidSecretary_Online_DimensionLP

namespace LinMatroidSecretary.Online

/-- Lemma 1 (PDF p. 8–9, printed 6–7): the expected-dimension identity for `µ_Y` defined by (2),
the pointwise equivalence of the Dimension Invariant Inequality with `g_p(L) ≤ 0`, and the
transfer from `L ≤ ⟨Y⟩` to every subspace. -/
theorem lemma_1 {F : Type*} [Field F] [Fintype F] {d : ℕ} {ι : Type*} [Fintype ι] [LinearOrder ι]
    (v : ι → Fin d → F) (Y : Finset ι) (k : ℕ) (hk : 1 ≤ k) (hkY : k < Y.card)
    (μ : ι → Dist F d) (hμ : ∀ e ∈ Y, IsDistOn (μ e) (spanOf v (Y.erase e)))
    (p : ι → Submodule F (Fin d → F) → ℝ)
    (hp : ∀ e ∈ Y, ∀ W ∈ (μ e).support, 0 ≤ p e W ∧ p e W ≤ 1) :
    (∀ L : Submodule F (Fin d → F),
      expect (muY v Y μ p) (fun U => dimInter U L) =
        (1 / (Y.card : ℝ)) * (((Y.card : ℝ) - (k : ℝ)) * (Module.finrank F ↥L : ℝ) +
          gp v Y k μ p L)) ∧
    (∀ L : Submodule F (Fin d → F), DimIneqAt (muY v Y μ p) Y.card k L ↔ gp v Y k μ p L ≤ 0) ∧
    ((∀ L : Submodule F (Fin d → F), L ≤ spanOf v Y → gp v Y k μ p L ≤ 0) →
      DimInvariant (muY v Y μ p) Y.card k) := by sorry

end LinMatroidSecretary.Online
