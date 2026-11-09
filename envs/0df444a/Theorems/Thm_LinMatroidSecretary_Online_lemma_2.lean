-- Prove2me | Theorems.Thm_LinMatroidSecretary_Online_lemma_2
-- name    : LinMatroidSecretary.Online.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:17:09.443167+00:00
-- url     : https://prove2.me/theorems/11de8e80-0b48-4cc2-b7ba-68986763074c
-- title:
--   Lemma 2 — LP(Y) is feasible
-- statement:
--   Let $k\ge1$ be the sample size, $F$ a finite field and $Y$ a set with $|Y|=i>k$. Suppose that for every $e\in Y$ the distribution $\mu_{Y-e}$ — a probability distribution on the subspaces of $\langle Y-e\rangle$ — satisfies the Dimension Invariant Inequality (1) (at size $|Y-e|=i-1$). Then $\mathrm{LP}(Y)$ is feasible: there is $p$ with
--   1. $0\le p(e,W)\le1$ for $e\in Y$, $W\in\operatorname{supp}\mu_{Y-e}$;
--   2. $p(e,W)=0$ when $e\notin\mathrm{OPT}(Y)$ or $v_e\in W$;
--   3. $\mathbb E_{W\sim\mu_{Y-e}}[p(e,W)]=k/(i-1)$ for every $e\in\mathrm{OPT}(Y)$;
--   4. $g_p(L)\le0$ for every $L\le\langle Y\rangle$.
--
--   This is what lets Algorithm 1 maintain the invariant forever.
--
--   Differences from the source:
--   - encoding: LP variables p(e, W) for e ∈ Y, W ∈ supp(µ_{Y−e}) → a function p on all pairs (e, W); only the values on those pairs are constrained or used; reason: the values off the LP variables enter no formula, so the instances are the same
--   - encoding: finite-dimensional vector spaces, subspaces, probability distributions and integer dimensions → vectors in Fin d → F, Submodule lattices, Finsupp distributions and real casts of finrank (including real subtraction in Δ); reason: every finite-dimensional represented instance has coordinates; over a finite field all subspaces form a finite set, so finite support loses no distributions, and casts preserve the exact dimensions
-- source:
--   Kristóf Bérczi, Shaddin Dughmi, Vasilis Livanos, Jose Soto, Victor Verdugo, The Strong Secretary Conjecture is True for Linear Matroids, STOC 2027 submission #608 (October 2026), Lemma 2, PDF p. 10 (printed p. 8); proof §3, PDF pp. 13–16

import Mathlib
import Definitions.Def_LinMatroidSecretary_Online_Setting
import Definitions.Def_LinMatroidSecretary_Online_DimensionLP

namespace LinMatroidSecretary.Online

/-- Lemma 2 (PDF p. 10, printed 8; proof §3): if `|Y| = i > k` and every `µ_{Y−e}` is a
probability distribution on the subspaces of `⟨Y − e⟩` satisfying the Dimension Invariant
Inequality (1) (at size `|Y − e| = i − 1`), then `LP(Y)` is feasible. -/
theorem lemma_2 {F : Type*} [Field F] [Fintype F] {d : ℕ} {ι : Type*} [Fintype ι]
    [LinearOrder ι] (v : ι → Fin d → F) (Y : Finset ι) (k : ℕ) (hk : 1 ≤ k) (hkY : k < Y.card)
    (μ : ι → Dist F d) (hμ : StandingFamily v Y k μ) :
    ∃ p : ι → Submodule F (Fin d → F) → ℝ, LPFeasible v Y k μ p := by sorry

end LinMatroidSecretary.Online
