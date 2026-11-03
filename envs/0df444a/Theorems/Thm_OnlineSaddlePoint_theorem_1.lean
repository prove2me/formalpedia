-- Prove2me | Theorems.Thm_OnlineSaddlePoint_theorem_1
-- name    : OnlineSaddlePoint.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:14:08.695578+00:00
-- url     : https://prove2.me/theorems/1f586430-3f11-4da4-8af0-abe425b65c8c
-- title:
--   Theorem 1 — SP-FTL has SP-Regret at most $\frac{8G^2}{H}(1+\log T)$
-- statement:
--   Let $E$, $F$ be real normed spaces, $X\subseteq E$, $Y\subseteq F$ compact, $T\ge1$, $H>0$, and let $\mathcal L_1,\dots,\mathcal L_T$ be any sequence of $H$-strongly convex-concave, $G$-Lipschitz functions on $X\times Y$. Then every run $(x_t,y_t)$ of Saddle-Point Follow-the-Leader satisfies
--
--   $$
--   \mathrm{SP\text{-}Regret}(T)=\Big|\sum_{t=1}^{T}\mathcal L_t(x_t,y_t)-\min_{x\in X}\max_{y\in Y}\sum_{t=1}^{T}\mathcal L_t(x,y)\Big|\le\frac{8G^2}{H}\,(1+\log T),
--   $$
--
--   where $\log$ is the natural logarithm.
--
--   The bound holds for every payoff sequence, so the payoffs may be chosen by an adaptive adversary that sees the previous iterates. It shows that jointly playing the saddle point of the games seen so far tracks the value of the hindsight game with only logarithmic cumulative error.
--
--   Differences from the source:
--   - generalization: $X\subset\mathbb R^{d_1}$, $Y\subset\mathbb R^{d_2}$ with any norm → $X$, $Y$ subsets of arbitrary real normed spaces $E$, $F$; reason: $\mathbb R^{d}$ with any norm is a real normed space, and no finite dimension is used
--   - generalization: $|\mathcal L(x_1,y_1)-\mathcal L(x_2,y_2)|\le G\|[x_1;y_1]-[x_2;y_2]\|$ → $|\mathcal L(x_1,y_1)-\mathcal L(x_2,y_2)|\le G(\|x_1-x_2\|+\|y_1-y_2\|)$ on $X\times Y$; reason: implied by the paper's form for every stacked norm with $\|[a;b]\|\le\|a\|+\|b\|$ (all $\ell_p$ norms); it is the form the proofs on pp.7, 9, 10 use
--   - generalization: $H$-strong convexity via subgradients, $f(x_1)\ge f(x_2)+\nabla f(x_2)^\top(x_1-x_2)+\frac H2\|x_1-x_2\|^2$ → Mathlib `StrongConvexOn` / `StrongConcaveOn` (the chord inequality with modulus $\frac H2 r^2$); reason: the subgradient form implies the chord form (apply it at $ax_1+bx_2$ and average), so the hypothesis is weaker
--   - encoding: "$H$-strongly" → $0<H$; reason: strong convexity presumes a positive modulus; only $H\le0$ is excluded
--   - encoding: $G$-Lipschitz → $G$-Lipschitz with $0\le G$; reason: a Lipschitz constant is nonnegative; the condition only excludes negative constants, which the paper never considers
--   - encoding: $\mathcal L_t : X\times Y\to\mathbb R$ → `L t : E → F → ℝ`, only its values on $X\times Y$ enter; reason: a function on $X\times Y$ extends to $E\times F$ arbitrarily; no hypothesis or conclusion reads values off $X\times Y$
--   - encoding: rounds $t=1,\dots,T$, iterates $(x_t,y_t)$, $t=1,\dots,T+1$ → $T\in\mathbb N$ with $1\le T$, sequences `x : ℕ → E`, `y : ℕ → F` read at $1,\dots,T+1$ (index $0$ unused); reason: the same indexing; the unused index carries no information
--   - encoding: $X$, $Y$ convex (and nonempty) → convexity carried by `ConvexOn`/`StrongConvexOn` (which include convexity of the set); nonemptiness by $x_1\in X$, $y_1\in Y$; reason: the same instances: with $Y$ nonempty and $T\ge1$ the payoff hypotheses already assert convexity of $X$ and $Y$
--   - encoding: $\min_{x\in X}\max_{y\in Y}$, $\arg\min$, $\arg\max$ → `sInf`/`sSup` of images in $\mathbb R$; $x_{t+1}$, $y_{t+1}$ any minimizer/maximizer; reason: under compactness and the Lipschitz bound the extrema are attained, so `sInf`/`sSup` are the paper's min/max
--   - encoding: $\log T$ → `Real.log T`; reason: the natural logarithm; the proof on p.10 writes $\ln T$
-- source:
--   Rivera Cardoso, Wang, Xu, The Online Saddle Point Problem and Online Convex Optimization with Knapsacks, arXiv:1806.08301v3, Theorem 1, p.6

import Mathlib
import Definitions.Def_OnlineSaddlePoint_spRegret
import Definitions.Def_OnlineSaddlePoint_IsStronglyConvexConcaveOn
import Definitions.Def_OnlineSaddlePoint_IsLipschitzPayoff
import Definitions.Def_OnlineSaddlePoint_IsSPFTLRun

namespace OnlineSaddlePoint

/-- **Theorem 1 (SP-FTL has logarithmic SP-Regret).** Rivera Cardoso, Wang, Xu,
arXiv:1806.08301v3, Theorem 1, p.6: "Let `{𝓛_t(x, y)}_{t=1}^T` be any sequence of `H`-strongly
convex-concave, `G`-Lipschitz functions. Then, the SP-FTL algorithm guarantees
`SP-Regret(T) = |∑_{t=1}^T 𝓛_t(x_t, y_t) − min_{x∈X} max_{y∈Y} ∑_{t=1}^T 𝓛_t(x, y)| ≤
(8G²/H)(1 + log T)`."

**Formalization Note.** `X ⊂ ℝ^{d₁}`, `Y ⊂ ℝ^{d₂}` with any norm are generalized to compact subsets
of arbitrary real normed spaces `E`, `F`; their convexity is part of Mathlib's `StrongConvexOn`
(inside `IsStronglyConvexConcaveOn`) and their nonemptiness is witnessed by the run. `H > 0` is the
paper's "strongly"; `log` is the natural logarithm `Real.log` (the proof on p.10 writes `ln T`).
The bound is on the absolute value, so both directions are asserted. -/
theorem theorem_1 {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (X : Set E) (Y : Set F) (L : ℕ → E → F → ℝ) (H G : ℝ) (T : ℕ) (x : ℕ → E) (y : ℕ → F)
    (hT : 1 ≤ T) (hX : IsCompact X) (hY : IsCompact Y) (hH : 0 < H)
    (hsc : ∀ t ∈ Finset.Icc 1 T, IsStronglyConvexConcaveOn X Y H (L t))
    (hlip : ∀ t ∈ Finset.Icc 1 T, IsLipschitzPayoff X Y G (L t))
    (hrun : IsSPFTLRun L X Y T x y) :
    spRegret L X Y T x y ≤ 8 * G ^ 2 / H * (1 + Real.log T) := by sorry

end OnlineSaddlePoint
