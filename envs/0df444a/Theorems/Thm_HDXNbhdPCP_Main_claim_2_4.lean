-- Prove2me | Theorems.Thm_HDXNbhdPCP_Main_claim_2_4
-- name    : HDXNbhdPCP.Main.claim_2_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:58:52.056204+00:00
-- url     : https://prove2.me/theorems/f596fb2b-bc75-4901-ae26-2b7ea56391b6
-- title:
--   Claim 2.4 — a bipartite $\lambda$-expander is a $\lambda^2$-sampler
-- statement:
--   Let $G=(L,R,E,\pi_G)$ be a weighted bipartite graph (a distribution of full support on its edge set $E\subseteq L\times R$, vertex sets the supports of its marginals) and let $\lambda\in\mathbb R$. If $G$ is a $\lambda$-expander, i.e. $\|Af\|_2\le\lambda\|f\|_2$ for every mean-zero $f:L\to\mathbb R$ where $(Af)(r)=\mathbb E_{\ell\sim r}f(\ell)$, then $G$ is a $\lambda^2$-sampler: for every $f:L\to[0,1]$ and every $\varepsilon>0$,
--   $$\Pr_{r\sim R}\Big[\big|\mathbb E_{\ell\sim r}f(\ell)-\mathbb E_{\ell\sim L}f(\ell)\big|>\varepsilon\Big]\le\frac{\lambda^2}{\varepsilon^2}\,\mathbb E_{\ell\sim L}f(\ell).$$
--
--   This is the standard passage from spectral expansion to sampling; it is used throughout the paper (Claims 2.18–2.20, Lemma 6.12, Theorem 6.1, Lemma 7.3).
--
--   Differences from the source:
--   - encoding: bipartite graph (L, R, E, π_G) with no isolated vertices → FinDist on L × R with IsProb; L, R are the supports of the marginals; reason: same objects; the support convention makes every vertex non-isolated
-- source:
--   Dikstein, Dinur, Hopkins, Singer, Sounder, shorter, and simpler PCPs from HDX neighborhoods, STOC 2027 submission (manuscript sha256 7dcb1b53…), p. 13, Claim 2.4

import Mathlib
import Definitions.Def_HDXNbhdPCP_Main_Complex

namespace HDXNbhdPCP.Main

/-- Claim 2.4: a bipartite `λ`-expander is a `λ²`-sampler. -/
theorem claim_2_4 {L R : Type} (G : BipGraph L R) (hG : FinDist.IsProb G) (lam : ℝ)
    (hexp : G.IsExpander lam) : G.IsSampler (lam ^ 2) := by sorry

end HDXNbhdPCP.Main
