-- Prove2me | Theorems.Thm_LooseHamHitting_Main_lemma_6_5
-- name    : LooseHamHitting.Main.lemma_6_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:19:06.15932+00:00
-- url     : https://prove2.me/theorems/0acc06fb-469f-44c9-bc75-1a0dd997abe0
-- title:
--   Lemma 6.5 — two independent uniform cycles from a large family share O(n/log d(G)) triples on average
-- statement:
--   Let $G$ be a 3-graph on $n$ vertices, $M$ a matching of $s\ge1$ pairs on the same vertex set, $\mathcal C$ a nonempty family of $(G,M)$-respecting mixed Hamilton cycles, and $C_1,C_2$ independent and uniform on $\mathcal C$. For every fixed $A\ge1$ and $B\ge0$ there is $C>0$ depending only on $A,B$ such that: if $s=o(n)$, $d(G)\to\infty$, $\Delta_1(G)\le Ad(G)$ and $\log|\mathcal C|\ge\frac{n-s}2\log d(G)-Bn$, then for sufficiently large $n$
--   $$E\big[|C_1\cap C_2|-s\big]\le C\,\frac n{\log d(G)}.$$
--
--   Formally: for all $A\ge1$, $B\ge0$ there are $C>0$, $\eta>0$ and $N$ such that the bound holds whenever $n\ge N$, $s\le\eta n$ and $d(G)\ge1/\eta$, besides the other hypotheses. The lemma controls the variance of cycle counts under random edge deletion (§10).
--
--   Differences from the source:
--   - encoding: s = o(n), d(G) → ∞, for sufficiently large n → ∃ η > 0, ∃ N (depending only on A, B): n ≥ N, s ≤ η n, d(G) ≥ 1/η; reason: equivalent to the statement over sequences of instances with C depending only on A, B
-- source:
--   León, Liu, Hitting time for loose Hamilton cycles in the random hypergraph process, arXiv:2610.29894v1, p. 24, Lemma 6.5

import Mathlib
import Definitions.Def_LooseHamHitting_Main_Hypergraph
import Definitions.Def_LooseHamHitting_Main_Entropy
import Definitions.Def_LooseHamHitting_Main_Marginals

set_option autoImplicit false

open Classical

namespace LooseHamHitting.Main

/-- Lemma 6.5: two independent uniform members of a large family of mixed Hamilton cycles share
few triples on average. `s = o(n)`, `d(G) → ∞` and "for sufficiently large `n`" are encoded
uniformly through `η` and `N`; `C` depends only on `A, B`. -/
theorem lemma_6_5 :
    ∀ A B : ℝ, 1 ≤ A → 0 ≤ B → ∃ C : ℝ, 0 < C ∧ ∃ η : ℝ, 0 < η ∧ ∃ N : ℕ,
      ∀ (β : Type*) (V : Finset β) (G M : Finset (Finset β)) (𝒞 : Finset (Finset (Finset β)))
        (n s : ℕ),
        V.card = n → M.card = s → IsThreeGraph V G → IsMatching V M → 1 ≤ s →
        𝒞 ⊆ mixedHamCycles V G M → 𝒞.Nonempty →
        N ≤ n → (s : ℝ) ≤ η * n → 1 / η ≤ avgDegree V G →
        (maxDegree V G : ℝ) ≤ A * avgDegree V G →
        ((n : ℝ) - s) / 2 * Real.log (avgDegree V G) - B * n ≤ Real.log 𝒞.card →
        overlapExcess 𝒞 s ≤ C * n / Real.log (avgDegree V G) := by sorry

end LooseHamHitting.Main
