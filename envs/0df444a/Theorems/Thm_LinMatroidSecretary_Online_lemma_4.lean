-- Prove2me | Theorems.Thm_LinMatroidSecretary_Online_lemma_4
-- name    : LinMatroidSecretary.Online.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:16:35.025048+00:00
-- url     : https://prove2.me/theorems/d7b91501-a1c5-48e5-9c1d-adc5da4d2a68
-- title:
--   Lemma 4 — uncrossing reduces LP(X) to chains
-- statement:
--   Under the standing hypotheses of §3 (sample size $k\ge1$; $|X|=i>k$; every $\mu_{X-e}$ a probability distribution on the subspaces of $\langle X-e\rangle$ satisfying (1)), suppose that for every chain of subspaces
--   $$L_1<L_2<\dots<L_s\le\langle X\rangle$$
--   there is $p\in P=P(X,\mu)$ with $g_p(L_j)\le0$ for every $j\in\{1,\dots,s\}$. Then there is a single $p\in P$ with $g_p(L)\le0$ for every $L\le\langle X\rangle$, i.e. $\mathrm{LP}(X)$ is feasible.
--
--   Lemma 4 reduces the feasibility of $\mathrm{LP}(X)$, which has one constraint per subspace of $\langle X\rangle$, to chains.
--
--   Differences from the source:
--   - encoding: LP variables p(e, W) for e ∈ Y, W ∈ supp(µ_{Y−e}) → a function p on all pairs (e, W); only the values on those pairs are constrained or used; reason: the values off the LP variables enter no formula, so the instances are the same
--   - encoding: chains C = {L1, …, Ls} with L1 < ··· < Ls ≤ ⟨X⟩ → lists of subspaces that are strictly increasing (List.IsChain (· < ·)), of any length s ≥ 0, all ≤ ⟨X⟩; reason: the empty chain only asks for some p ∈ P, which the one-element chain {0} already provides, so the hypothesis is unchanged
--   - encoding: finite-dimensional vector spaces, subspaces, probability distributions and integer dimensions → vectors in Fin d → F, Submodule lattices, Finsupp distributions and real casts of finrank (including real subtraction in Δ); reason: every finite-dimensional represented instance has coordinates; over a finite field all subspaces form a finite set, so finite support loses no distributions, and casts preserve the exact dimensions
-- source:
--   Kristóf Bérczi, Shaddin Dughmi, Vasilis Livanos, Jose Soto, Victor Verdugo, The Strong Secretary Conjecture is True for Linear Matroids, STOC 2027 submission #608 (October 2026), Lemma 4, PDF p. 13 (printed p. 11); proof PDF p. 14

import Mathlib
import Definitions.Def_LinMatroidSecretary_Online_Setting
import Definitions.Def_LinMatroidSecretary_Online_DimensionLP

namespace LinMatroidSecretary.Online

/-- Lemma 4 (PDF p. 13, printed 11; proof p. 14): uncrossing. Under the standing hypotheses of §3,
if every chain `L₁ < ⋯ < L_s ≤ ⟨X⟩` admits a `p ∈ P` with `g_p(L_j) ≤ 0` for all `j`, then a
single `p ∈ P` satisfies `g_p(L) ≤ 0` for every `L ≤ ⟨X⟩`. -/
theorem lemma_4 {F : Type*} [Field F] [Fintype F] {d : ℕ} {ι : Type*} [Fintype ι]
    [LinearOrder ι] (v : ι → Fin d → F) (X : Finset ι) (k : ℕ) (hk : 1 ≤ k) (hkX : k < X.card)
    (μ : ι → Dist F d) (hμ : StandingFamily v X k μ)
    (hchain : ∀ C : List (Submodule F (Fin d → F)), C.IsChain (· < ·) →
      (∀ L ∈ C, L ≤ spanOf v X) →
      ∃ p : ι → Submodule F (Fin d → F) → ℝ, InP v X k μ p ∧ ∀ L ∈ C, gp v X k μ p L ≤ 0) :
    ∃ p : ι → Submodule F (Fin d → F) → ℝ, InP v X k μ p ∧
      ∀ L : Submodule F (Fin d → F), L ≤ spanOf v X → gp v X k μ p L ≤ 0 := by sorry

end LinMatroidSecretary.Online
