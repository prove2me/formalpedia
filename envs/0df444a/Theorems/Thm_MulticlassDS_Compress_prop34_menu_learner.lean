-- Prove2me | Theorems.Thm_MulticlassDS_Compress_prop34_menu_learner
-- name    : MulticlassDS.Compress.prop34_menu_learner
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:21:50.645578+00:00
-- url     : https://prove2.me/theorems/a88e98a7-af47-489a-9ae8-b461c6b6f0cb
-- title:
--   Proposition 34, p. 21 — given a p-menu, the one-inclusion algorithm errs with probability ≤ 20 d_N log(p)/n
-- statement:
--   Let $\mathcal H\subseteq\mathcal Y^{\mathcal X}$ have Natarajan dimension $d_N<\infty$ and let $\mu$ be a $p$-menu. For every distribution $\mathcal D$ over $\mathcal X\times\mathcal Y$ that is realizable by both $\mathcal H$ and $\mu$, and every integer $n>0$,
--   $$\Pr_{(S,(x,y))\sim\mathcal D^{n+1}}\big[h_S(x)\neq y\big]\ \le\ \frac{20\,d_N\log(p)}{n},$$
--   where $h_S = \mathcal A_{\mathcal H,\mu}(S)$ is the one-inclusion algorithm given the menu (Algorithm 3) and the logarithm is base $2$.
--
--   This weak learner, run on many subsamples, gives the menu compression scheme of Lemma 40.
--
--   **Formalization Note** Distributions are discrete (`PMF`); the bound is compared in $[0,\infty]$ through `ENNReal.ofReal`. The algorithm is parametrized by a permutation-equivariant choice `C` of minimal orientations of the menu-restricted classes $\mathcal H'$, and the statement holds for every such choice. The label set is assumed non-empty, needed only to define the algorithm's default output.
-- source:
--   Brukhim, Carmon, Dinur, Moran, Yehudayoff, A Characterization of Multiclass Learnability, arXiv:2203.01550v1, p. 21, Proposition 34 (with Algorithm 3, p. 21)

import Mathlib
import Definitions.Def_MulticlassDS_Compress_Dimensions
import Definitions.Def_MulticlassDS_Compress_Compression
import Definitions.Def_MulticlassDS_Compress_OneInclusion
import Definitions.Def_MulticlassDS_Compress_Probability

namespace MulticlassDS.Compress

theorem prop34_menu_learner {X Y : Type*} [Nonempty Y] (H : Set (X → Y)) (dN : ℕ)
    (hN : natarajanDim H = dN) (μ : X → Set Y) (p : ℕ) (hμ : IsMenu μ p)
    (C : OIGChoice (menuFamily H μ)) (D : PMF (X × Y)) (hDH : IsRealizableDist H D)
    (hDμ : MenuRealizableDist μ D) (n : ℕ) (hn : 0 < n) :
    iidProb D (n + 1)
        {s | oigPredict C (Fin.init s) (s (Fin.last n)).1 ≠ (s (Fin.last n)).2} ≤
      ENNReal.ofReal (20 * dN * Real.logb 2 p / n) := by sorry

end MulticlassDS.Compress
