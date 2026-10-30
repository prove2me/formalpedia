-- Prove2me | Theorems.Thm_OnlineCRS_Combine_chi_antitone_first
-- name    : OnlineCRS.Combine.chi_antitone_first
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:26:37.39228+00:00
-- url     : https://prove2.me/theorems/991ad0ba-10c9-4ed7-9031-65f62256f36a
-- title:
--   $\chi_e$ is non-increasing in its first argument
-- statement:
--   Let $e\in N$, let $A\subseteq A'\subseteq N$ and let $\mathcal F,\mathcal F'$ be families of subsets of $N$. Then
--   $$\chi_e(A',\mathcal F,\mathcal F')\ \Longrightarrow\ \chi_e(A,\mathcal F,\mathcal F').$$
--
--   Thus each event $\{\chi_e(R,\mathcal F,\mathcal F')\}$ is a decreasing event of the random set $R$, which is what the FKG inequality in the proof of Lemma 2.11 needs.
--
--   Differences from the source: none.
-- source:
--   Feldman, Svensson, Zenklusen, Online Contention Resolution Schemes, arXiv:1508.00142v2, proof of Lemma 2.11 (unnumbered step), p. 16

import Mathlib
import Definitions.Def_OnlineCRS_Combine_chi

namespace OnlineCRS.Combine

/-- **`χ_e` is non-increasing in its first argument.**
Feldman, Svensson, Zenklusen, *Online Contention Resolution Schemes*, arXiv:1508.00142v2, proof of Lemma 2.11, p. 16 (unnumbered): "Next, observe that `χ_e` is also non-increasing in
its first argument (when the other two arguments are fixed)."

If `A ⊆ A'` then `χ_e(A', G, G')` implies `χ_e(A, G, G')`. -/
theorem chi_antitone_first {N : Type*} [DecidableEq N] (e : N) {A A' : Finset N}
    {G G' : Finset (Finset N)} (h : A ⊆ A') (hχ : chi e A' G G') : chi e A G G' := by sorry

end OnlineCRS.Combine
