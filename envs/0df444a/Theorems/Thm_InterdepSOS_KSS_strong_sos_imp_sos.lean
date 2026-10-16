-- Prove2me | Theorems.Thm_InterdepSOS_KSS_strong_sos_imp_sos
-- name    : InterdepSOS.KSS.strong_sos_imp_sos
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T12:36:47.063473+00:00
-- url     : https://prove2.me/theorems/ee178657-aefc-4958-b5ba-87b4eaf321d5
-- title:
--   §6, p. 19 — strong-SOS implies SOS on the signal grid
-- statement:
--   Let $w$ be a real function of signal profiles in $\{0,\dots,k-1\}^n$. If $w$ is strong-SOS on the grid, i.e. for every coordinate $j$, every $\delta\ge0$ and grid profiles $\mathbf s'\le\mathbf s$ with $s_j+\delta<k$,
--   $$w(\mathbf s_{-j},s_j+\delta)-w(\mathbf s)\le w(\mathbf s'_{-j},s'_j+\delta)-w(\mathbf s'),$$
--   then $w$ is SOS on the grid: for every $j$, $x,\delta\ge0$ with $x+\delta<k$, and grid profiles $\mathbf s,\mathbf s'$ with $s'_l\le s_l$ for $l\ne j$,
--   $$w(\mathbf s_{-j},x+\delta)-w(\mathbf s_{-j},x)\le w(\mathbf s'_{-j},x+\delta)-w(\mathbf s'_{-j},x).$$
--
--   This is the remark on p. 19 that inequality (6), proved from SOS, also holds under strong-SOS. It is what makes the decomposition (7) and the Random Sampling bound of Lemma 6.3 available for strong-SOS valuations.
--
--   **Formalization Note** The milestone quotes the sentence of p. 19 that carries the claim; the sentence sits inside the derivation of (6)–(7). The present statement is the implication between the two valuation classes, not (6)–(7) themselves, which belong to the companion mission on k-HL.
-- source:
--   Eden, Feldman, Fiat, Goldner, Karlin, Combinatorial Auctions with Interdependent Valuations: SOS to the Rescue, arXiv:1903.08384v2 (2019), p. 19, §6, sentence after display (7); Definitions 2.13–2.14, pp. 11–12

import Mathlib
import Definitions.Def_InterdepSOS_KSS_Setting

namespace InterdepSOS.KSS
theorem strong_sos_imp_sos {n : ℕ} (k : ℕ) (w : InterdepSOS.KHL.Signal n → ℝ) (h : IsStrongSOS k w) :
    InterdepSOS.KHL.IsSOS k w := by sorry
end InterdepSOS.KSS
