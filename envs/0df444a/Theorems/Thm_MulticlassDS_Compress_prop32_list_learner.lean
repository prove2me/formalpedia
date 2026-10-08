-- Prove2me | Theorems.Thm_MulticlassDS_Compress_prop32_list_learner
-- name    : MulticlassDS.Compress.prop32_list_learner
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:21:39.694209+00:00
-- url     : https://prove2.me/theorems/fdb9a65f-4405-4537-9abf-2ad4964b5023
-- title:
--   Proposition 32, p. 20 — finite DS dimension implies list PAC learning with list size C(n, t) and success probability (t+1)/(d+t+1)
-- statement:
--   Let $\mathcal H\subseteq\mathcal Y^{\mathcal X}$ have DS dimension $d<\infty$ and let $t\in\mathbb N$. The algorithm $\mathcal L_{\mathcal H,t}$ (Algorithm 2) is a list PAC learner for $\mathcal H$ with sample size $n = d+t$, list size $p = \binom{n}{t}$ and success probability
--   $$\alpha = \frac{t+1}{d+t+1}.$$
--   That is, its menus have at most $\binom{d+t}{t}$ labels, and for every $\mathcal H$-realizable distribution $\mathcal D$,
--   $$\Pr_{(S,(x,y))\sim\mathcal D^{d+t+1}}\big[y\in\mu_S(x)\big]\ \ge\ \frac{t+1}{d+t+1}.$$
--
--   The list learner is the first component of the sample compression scheme: boosted, it yields the list compression scheme of Lemma 39.
--
--   **Formalization Note** Distributions are discrete (`PMF`). The learner uses the one-inclusion algorithm with a permutation-equivariant choice `C` of minimal orientations, and the statement holds for every such choice. The label set is assumed non-empty, needed only to define the one-inclusion algorithm's default output. $t = 0$ is allowed, as on the page.
-- source:
--   Brukhim, Carmon, Dinur, Moran, Yehudayoff, A Characterization of Multiclass Learnability, arXiv:2203.01550v1, p. 20, Proposition 32 (with Definition 31, p. 19, and Algorithm 2, p. 20)

import Mathlib
import Definitions.Def_MulticlassDS_Compress_Dimensions
import Definitions.Def_MulticlassDS_Compress_Compression
import Definitions.Def_MulticlassDS_Compress_OneInclusion
import Definitions.Def_MulticlassDS_Compress_Probability

namespace MulticlassDS.Compress

theorem prop32_list_learner {X Y : Type*} [Nonempty Y] (H : Set (X → Y)) (d t : ℕ)
    (hd : dsDim H = d) (C : OIGChoice (projFamily H)) :
    IsListPACLearner H (d + t) (Nat.choose (d + t) t) (((t : ℝ) + 1) / (d + t + 1))
      (listMenu C d t) := by sorry

end MulticlassDS.Compress
