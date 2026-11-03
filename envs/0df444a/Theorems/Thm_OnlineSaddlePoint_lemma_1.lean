-- Prove2me | Theorems.Thm_OnlineSaddlePoint_lemma_1
-- name    : OnlineSaddlePoint.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:13:41.388225+00:00
-- url     : https://prove2.me/theorems/b87dbb73-9f7e-462e-810b-0015fd1a3942
-- title:
--   Lemma 1 — Follow-the-Leader vs Be-the-Leader bound (4) for SP-FTL
-- statement:
--   Let $E$, $F$ be real normed spaces, $X\subseteq E$, $Y\subseteq F$ compact, $T\ge1$, and let $\mathcal L_1,\dots,\mathcal L_T$ be convex-concave and $G$-Lipschitz on $X\times Y$. Let $(x_t,y_t)_{t=1}^{T+1}$ be a run of Saddle-Point Follow-the-Leader. Then
--
--   $$
--   -G\sum_{t=1}^{T}\|x_t-x_{t+1}\|\;\le\;\sum_{t=1}^{T}\mathcal L_t(x_{t+1},y_{t+1})-\min_{x\in X}\max_{y\in Y}\sum_{t=1}^{T}\mathcal L_t(x,y)\;\le\;G\sum_{t=1}^{T}\|y_t-y_{t+1}\|.
--   $$
--
--   The middle quantity is the regret of the "Be-the-Leader" actions $(x_{t+1},y_{t+1})$, which look one step ahead. The lemma bounds it on both sides by the movement of the iterates; combined with a bound on that movement it gives the regret of SP-FTL itself.
--
--   Differences from the source:
--   - generalization: $X\subset\mathbb R^{d_1}$, $Y\subset\mathbb R^{d_2}$ with any norm → $X$, $Y$ subsets of arbitrary real normed spaces $E$, $F$; reason: $\mathbb R^{d}$ with any norm is a real normed space, and no finite dimension is used
--   - generalization: $|\mathcal L(x_1,y_1)-\mathcal L(x_2,y_2)|\le G\|[x_1;y_1]-[x_2;y_2]\|$ → $|\mathcal L(x_1,y_1)-\mathcal L(x_2,y_2)|\le G(\|x_1-x_2\|+\|y_1-y_2\|)$ on $X\times Y$; reason: implied by the paper's form for every stacked norm with $\|[a;b]\|\le\|a\|+\|b\|$ (all $\ell_p$ norms); it is the form the proofs on pp.7, 9, 10 use
--   - encoding: $G$-Lipschitz → $G$-Lipschitz with $0\le G$; reason: a Lipschitz constant is nonnegative; the condition only excludes negative constants, which the paper never considers
--   - encoding: $\mathcal L_t : X\times Y\to\mathbb R$ → `L t : E → F → ℝ`, only its values on $X\times Y$ enter; reason: a function on $X\times Y$ extends to $E\times F$ arbitrarily; no hypothesis or conclusion reads values off $X\times Y$
--   - encoding: rounds $t=1,\dots,T$, iterates $(x_t,y_t)$, $t=1,\dots,T+1$ → $T\in\mathbb N$ with $1\le T$, sequences `x : ℕ → E`, `y : ℕ → F` read at $1,\dots,T+1$ (index $0$ unused); reason: the same indexing; the unused index carries no information
--   - encoding: $X$, $Y$ convex (and nonempty) → convexity carried by `ConvexOn`/`StrongConvexOn` (which include convexity of the set); nonemptiness by $x_1\in X$, $y_1\in Y$; reason: the same instances: with $Y$ nonempty and $T\ge1$ the payoff hypotheses already assert convexity of $X$ and $Y$
--   - encoding: $\min_{x\in X}\max_{y\in Y}$, $\arg\min$, $\arg\max$ → `sInf`/`sSup` of images in $\mathbb R$; $x_{t+1}$, $y_{t+1}$ any minimizer/maximizer; reason: under compactness and the Lipschitz bound the extrema are attained, so `sInf`/`sSup` are the paper's min/max
-- source:
--   Rivera Cardoso, Wang, Xu, The Online Saddle Point Problem and Online Convex Optimization with Knapsacks, arXiv:1806.08301v3, Lemma 1, p.6, display (4)

import Mathlib
import Definitions.Def_OnlineSaddlePoint_cumPayoff
import Definitions.Def_OnlineSaddlePoint_minimaxValue
import Definitions.Def_OnlineSaddlePoint_IsConvexConcaveOn
import Definitions.Def_OnlineSaddlePoint_IsLipschitzPayoff
import Definitions.Def_OnlineSaddlePoint_IsSPFTLRun

namespace OnlineSaddlePoint

/-- **Lemma 1 (Follow-the-Leader vs Be-the-Leader for SP-FTL).** Rivera Cardoso, Wang, Xu,
arXiv:1806.08301v3, Lemma 1, p.6: "Let `{𝓛_t}_{t=1}^T` be an arbitrary sequence of convex-concave
functions that are `G`-Lipschitz with respect to norm `‖·‖`. Here, `𝓛_t : X × Y → ℝ`, where
`X ⊂ ℝ^{d₁}` and `Y ⊂ ℝ^{d₂}` are convex compact sets. Let `{(x_t, y_t)}_{t=1}^T` be the iterates of
SP-FTL when run on the sequence of functions `{𝓛_t}_{t=1}^T`. It holds that
`−G ∑_{t=1}^T ‖x_t − x_{t+1}‖ ≤ ∑_{t=1}^T 𝓛_t(x_{t+1}, y_{t+1}) − min_{x∈X} max_{y∈Y} ∑_{t=1}^T 𝓛_t(x, y)
≤ G ∑_{t=1}^T ‖y_t − y_{t+1}‖`. (4)"

**Formalization Note.** `ℝ^{d₁}`, `ℝ^{d₂}` with any norm are generalized to arbitrary real normed
spaces `E`, `F`. The Lipschitz hypothesis is `IsLipschitzPayoff` (sum-of-norms form, implied by the
paper's). Convexity of `X`, `Y` is carried by `ConvexOn`/`ConcaveOn` inside `IsConvexConcaveOn`;
nonemptiness by the run's `x 1 ∈ X`, `y 1 ∈ Y`. Both inequalities of (4) are stated. -/
theorem lemma_1 {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (X : Set E) (Y : Set F) (L : ℕ → E → F → ℝ) (G : ℝ) (T : ℕ) (x : ℕ → E) (y : ℕ → F)
    (hT : 1 ≤ T) (hX : IsCompact X) (hY : IsCompact Y)
    (hcc : ∀ t ∈ Finset.Icc 1 T, IsConvexConcaveOn X Y (L t))
    (hlip : ∀ t ∈ Finset.Icc 1 T, IsLipschitzPayoff X Y G (L t))
    (hrun : IsSPFTLRun L X Y T x y) :
    -G * ∑ t ∈ Finset.Icc 1 T, ‖x t - x (t + 1)‖ ≤
        ∑ t ∈ Finset.Icc 1 T, L t (x (t + 1)) (y (t + 1)) - minimaxValue X Y (cumPayoff L T) ∧
      ∑ t ∈ Finset.Icc 1 T, L t (x (t + 1)) (y (t + 1)) - minimaxValue X Y (cumPayoff L T) ≤
        G * ∑ t ∈ Finset.Icc 1 T, ‖y t - y (t + 1)‖ := by sorry

end OnlineSaddlePoint
