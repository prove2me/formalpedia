-- Prove2me | Theorems.Thm_LinMatroidSecretary_Online_chain_feasible
-- name    : LinMatroidSecretary.Online.chain_feasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:16:51.755517+00:00
-- url     : https://prove2.me/theorems/80bb0b39-2f49-4e3a-8fe3-4363214acbfe
-- title:
--   §3 (8)–(13) — every chain admits a point of P with g_p ≤ 0 on it
-- statement:
--   Under the standing hypotheses of §3 (sample size $k\ge1$; $|X|=i>k$; every $\mu_{X-e}$ a probability distribution on the subspaces of $\langle X-e\rangle$ satisfying (1)), for every chain of subspaces $L_1<\dots<L_s\le\langle X\rangle$ there is a point $p\in P=P(X,\mu)$ with
--   $$g_p(L_j)\le0\qquad\text{for every }j\in\{1,\dots,s\}.$$
--
--   This is exactly the hypothesis of Lemma 4; together they prove Lemma 2. (In the paper the point is the greedy assignment (8) along the safety order of the chain.)
--
--   Differences from the source:
--   - encoding: LP variables p(e, W) for e ∈ Y, W ∈ supp(µ_{Y−e}) → a function p on all pairs (e, W); only the values on those pairs are constrained or used; reason: the values off the LP variables enter no formula, so the instances are the same
--   - encoding: a chain L1 < ··· < Ls ≤ ⟨X⟩ → a strictly increasing list of subspaces (List.IsChain (· < ·)), all ≤ ⟨X⟩, of any length; reason: lists are the chains; the empty list asks only for a point of P
--   - encoding: finite-dimensional vector spaces, subspaces, probability distributions and integer dimensions → vectors in Fin d → F, Submodule lattices, Finsupp distributions and real casts of finrank (including real subtraction in Δ); reason: every finite-dimensional represented instance has coordinates; over a finite field all subspaces form a finite set, so finite support loses no distributions, and casts preserve the exact dimensions
-- source:
--   Kristóf Bérczi, Shaddin Dughmi, Vasilis Livanos, Jose Soto, Victor Verdugo, The Strong Secretary Conjecture is True for Linear Matroids, STOC 2027 submission #608 (October 2026), §3, the construction (8)–(13), PDF pp. 14–16 (printed pp. 12–14)

import Mathlib
import Definitions.Def_LinMatroidSecretary_Online_Setting
import Definitions.Def_LinMatroidSecretary_Online_DimensionLP

namespace LinMatroidSecretary.Online

/-- §3 chain construction (PDF pp. 14–16, printed 12–14, (8)–(13)): under the standing hypotheses
of §3, for every chain `L₁ < ⋯ < L_s ≤ ⟨X⟩` there is `p ∈ P` with `g_p(L_j) ≤ 0` for all `j`. -/
theorem chain_feasible {F : Type*} [Field F] [Fintype F] {d : ℕ} {ι : Type*} [Fintype ι]
    [LinearOrder ι] (v : ι → Fin d → F) (X : Finset ι) (k : ℕ) (hk : 1 ≤ k) (hkX : k < X.card)
    (μ : ι → Dist F d) (hμ : StandingFamily v X k μ)
    (C : List (Submodule F (Fin d → F))) (hC : C.IsChain (· < ·))
    (hCX : ∀ L ∈ C, L ≤ spanOf v X) :
    ∃ p : ι → Submodule F (Fin d → F) → ℝ, InP v X k μ p ∧ ∀ L ∈ C, gp v X k μ p L ≤ 0 := by sorry

end LinMatroidSecretary.Online
