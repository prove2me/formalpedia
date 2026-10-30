-- Prove2me | Theorems.Thm_OnlineCRS_Combine_chi_antitone_third
-- name    : OnlineCRS.Combine.chi_antitone_third
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:26:06.996984+00:00
-- url     : https://prove2.me/theorems/a2a17291-15ed-48c7-8cb7-4ac95829d880
-- title:
--   $\chi_e$ is non-increasing in its third argument
-- statement:
--   Let $e\in N$, $A\subseteq N$ and let $\mathcal F,\mathcal F',\mathcal F''$ be families of subsets of $N$ with $\mathcal F'\subseteq\mathcal F''$. Then
--   $$\chi_e(A,\mathcal F,\mathcal F'')\ \Longrightarrow\ \chi_e(A,\mathcal F,\mathcal F').$$
--
--   In the proof of Lemma 2.11 this gives $\Pr[\chi_e(R(x),\mathcal F_{\pi^1,x},\mathcal F_{\pi^1,x}\cap\mathcal F_{\pi^2,x})]\ge\Pr[\chi_e(R(x),\mathcal F_{\pi^1,x},\mathcal F_{\pi^1,x})]\ge c_1$.
--
--   Differences from the source: none.
-- source:
--   Feldman, Svensson, Zenklusen, Online Contention Resolution Schemes, arXiv:1508.00142v2, proof of Lemma 2.11 (unnumbered step), p. 16

import Mathlib
import Definitions.Def_OnlineCRS_Combine_chi

namespace OnlineCRS.Combine

/-- **`χ_e` is non-increasing in its third argument.**
Feldman, Svensson, Zenklusen, *Online Contention Resolution Schemes*, arXiv:1508.00142v2, proof of Lemma 2.11, p. 16 (unnumbered): "the first inequality follows since `χ_e` is a
non-increasing function of its third argument (when the other two arguments are fixed)."

If `G' ⊆ G''` then `χ_e(A, G, G'')` implies `χ_e(A, G, G')`. -/
theorem chi_antitone_third {N : Type*} [DecidableEq N] (e : N) (A : Finset N)
    {G G' G'' : Finset (Finset N)} (h : G' ⊆ G'') (hχ : chi e A G G'') : chi e A G G' := by sorry

end OnlineCRS.Combine
