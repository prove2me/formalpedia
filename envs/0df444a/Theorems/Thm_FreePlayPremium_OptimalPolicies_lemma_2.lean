-- Prove2me | Theorems.Thm_FreePlayPremium_OptimalPolicies_lemma_2
-- name    : FreePlayPremium.OptimalPolicies.lemma_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T23:27:54.671187+00:00
-- url     : https://prove2.me/theorems/690abec8-ae24-4188-ac14-47f2d2d2a819
-- title:
--   Lemma 2 — player-preferred equilibrium with stronger upward comparison
-- statement:
--   Let $0<\alpha_d<\alpha_u<v$ and $p\ge0$. The player-preferred stable premium share is
--   $$S(p)=\begin{cases}1,&p\le\alpha_d,\\0,&p>\alpha_d.\end{cases}$$
--   More precisely, this share belongs to $[0,1]$, and for every $s\in[0,1]$, $s$ is stable and maximizes the players' common equilibrium utility among stable equilibria if and only if $s=S(p)$. Thus the selected equilibrium exists. The claim allows multiple unselected stable equilibria; it does not assert uniqueness of stability itself.
--
--   Differences from the source:
--   - encoding: utilities contain a common friction term -1/n for positive population → stability uses the algebraic premium-minus-free difference and preference uses average utility without the common friction; reason: the common term cancels in both comparisons, so no positive population instance changes
-- source:
--   Mai and Hu (2022), Optimizing Free-to-Play Multiplayer Games with Premium Subscription, Management Science, https://doi.org/10.1287/mnsc.2022.4510, Lemma 2, printed p. 8 (PDF p. 8); proof printed p. 33 (PDF p. 33)

import Definitions.Def_FreePlayPremium_OptimalPolicies_Players

open Set

namespace FreePlayPremium.OptimalPolicies

theorem lemma_2 (P : PlayerParameters) (hP : P.Valid) (hdu : P.down < P.up)
    (p : ℝ) (hp : 0 ≤ p) :
    premiumShare P p ∈ Icc (0 : ℝ) 1 ∧
    ∀ s ∈ Icc (0 : ℝ) 1, SelectedStable P p s ↔ s = premiumShare P p := by sorry

end FreePlayPremium.OptimalPolicies
