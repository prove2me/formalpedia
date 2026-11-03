-- Prove2me | Theorems.Thm_OnlineSaddlePoint_spftl_isSaddlePoint
-- name    : OnlineSaddlePoint.spftl_isSaddlePoint
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:13:55.469201+00:00
-- url     : https://prove2.me/theorems/19639f61-b17b-4675-b7ff-3b65eb6de01f
-- title:
--   p.6 — SP-FTL plays the (unique) saddle point of the games observed so far
-- statement:
--   Let $E$, $F$ be real normed spaces, $X\subseteq E$, $Y\subseteq F$ compact, $T\ge1$, and let $\mathcal L_1,\dots,\mathcal L_T$ be convex-concave and $G$-Lipschitz on $X\times Y$. Let $(x_t,y_t)_{t=1}^{T+1}$ be a run of Saddle-Point Follow-the-Leader. Then for every $t=1,\dots,T$:
--
--   1. $(x_{t+1},y_{t+1})$ is a saddle point of $J_t=\sum_{\tau=1}^{t}\mathcal L_\tau$ on $X\times Y$, that is,
--   $$
--   J_t(x_{t+1},y)\le J_t(x_{t+1},y_{t+1})\le J_t(x,y_{t+1})\qquad\text{for all }x\in X,\ y\in Y;
--   $$
--   2. its value is the value of the game:
--   $$
--   J_t(x_{t+1},y_{t+1})=\min_{x\in X}\max_{y\in Y}J_t(x,y)=\max_{y\in Y}\min_{x\in X}J_t(x,y);
--   $$
--   3. if moreover every $\mathcal L_t$ is $H$-strongly convex-concave for some $H>0$, then $(x_{t+1},y_{t+1})$ is the only saddle point of $J_t$ in $X\times Y$.
--
--   This is what makes SP-FTL a Follow-the-Leader method for games: each round the players jointly play the equilibrium of the games observed so far. The proofs of Lemmas 1 and 2 use it in every step.
--
--   Differences from the source:
--   - generalization: in §4.1 the payoffs are $H$-strongly convex-concave → the saddle-point and value clauses assume only convex-concave $G$-Lipschitz payoffs; uniqueness assumes $H$-strong convexity-concavity with $H>0$; reason: the proof of Lemma 1 (p.7) uses the saddle-point clause under convex-concavity; with strong convexity-concavity the statement specializes to the p.6 sentence
--   - generalization: $X\subset\mathbb R^{d_1}$, $Y\subset\mathbb R^{d_2}$ with any norm → $X$, $Y$ subsets of arbitrary real normed spaces $E$, $F$; reason: $\mathbb R^{d}$ with any norm is a real normed space, and no finite dimension is used
--   - generalization: $|\mathcal L(x_1,y_1)-\mathcal L(x_2,y_2)|\le G\|[x_1;y_1]-[x_2;y_2]\|$ → $|\mathcal L(x_1,y_1)-\mathcal L(x_2,y_2)|\le G(\|x_1-x_2\|+\|y_1-y_2\|)$ on $X\times Y$; reason: implied by the paper's form for every stacked norm with $\|[a;b]\|\le\|a\|+\|b\|$ (all $\ell_p$ norms); it is the form the proofs on pp.7, 9, 10 use
--   - generalization: $H$-strong convexity via subgradients, $f(x_1)\ge f(x_2)+\nabla f(x_2)^\top(x_1-x_2)+\frac H2\|x_1-x_2\|^2$ → Mathlib `StrongConvexOn` / `StrongConcaveOn` (the chord inequality with modulus $\frac H2 r^2$); reason: the subgradient form implies the chord form (apply it at $ax_1+bx_2$ and average), so the hypothesis is weaker
--   - encoding: "$H$-strongly" → $0<H$; reason: strong convexity presumes a positive modulus; only $H\le0$ is excluded
--   - encoding: $G$-Lipschitz → $G$-Lipschitz with $0\le G$; reason: a Lipschitz constant is nonnegative; the condition only excludes negative constants, which the paper never considers
--   - encoding: $\mathcal L_t : X\times Y\to\mathbb R$ → `L t : E → F → ℝ`, only its values on $X\times Y$ enter; reason: a function on $X\times Y$ extends to $E\times F$ arbitrarily; no hypothesis or conclusion reads values off $X\times Y$
--   - encoding: rounds $t=1,\dots,T$, iterates $(x_t,y_t)$, $t=1,\dots,T+1$ → $T\in\mathbb N$ with $1\le T$, sequences `x : ℕ → E`, `y : ℕ → F` read at $1,\dots,T+1$ (index $0$ unused); reason: the same indexing; the unused index carries no information
--   - encoding: $X$, $Y$ convex (and nonempty) → convexity carried by `ConvexOn`/`StrongConvexOn` (which include convexity of the set); nonemptiness by $x_1\in X$, $y_1\in Y$; reason: the same instances: with $Y$ nonempty and $T\ge1$ the payoff hypotheses already assert convexity of $X$ and $Y$
--   - encoding: $\min_{x\in X}\max_{y\in Y}$, $\arg\min$, $\arg\max$ → `sInf`/`sSup` of images in $\mathbb R$; $x_{t+1}$, $y_{t+1}$ any minimizer/maximizer; reason: under compactness and the Lipschitz bound the extrema are attained, so `sInf`/`sSup` are the paper's min/max
-- source:
--   Rivera Cardoso, Wang, Xu, The Online Saddle Point Problem and Online Convex Optimization with Knapsacks, arXiv:1806.08301v3, p.6 ("play the (unique) saddle point of the sum of the games observed so far"), with p.2 and (3), p.5

import Mathlib
import Definitions.Def_OnlineSaddlePoint_cumPayoff
import Definitions.Def_OnlineSaddlePoint_minimaxValue
import Definitions.Def_OnlineSaddlePoint_maximinValue
import Definitions.Def_OnlineSaddlePoint_IsConvexConcaveOn
import Definitions.Def_OnlineSaddlePoint_IsStronglyConvexConcaveOn
import Definitions.Def_OnlineSaddlePoint_IsLipschitzPayoff
import Definitions.Def_OnlineSaddlePoint_IsSPFTLRun

namespace OnlineSaddlePoint

/-- **SP-FTL plays the (unique) saddle point of the games observed so far.** Rivera Cardoso,
Wang, Xu, arXiv:1806.08301v3, p.6: "in SP-FTL both players update jointly and play the (unique)
saddle point of the sum of the games observed so far"; with p.2 ("there exists a saddle point
`(x*, y*) ∈ X × Y` such that `min_{x∈X} max_{y∈Y} ∑ 𝓛_t(x, y) = ∑ 𝓛_t(x*, y*) =
max_{y∈Y} min_{x∈X} ∑ 𝓛_t(x, y)`") and the saddle-point definition (3), p.5.

Under the hypotheses of Lemma 1 (each `𝓛_t` convex-concave and `G`-Lipschitz, `X`, `Y` compact),
for every round `t = 1, …, T` of an SP-FTL run, `(x_{t+1}, y_{t+1})` is a saddle point of
`∑_{τ=1}^t 𝓛_τ` on `X × Y`, and its value equals both the min-max and the max-min value. If moreover
every `𝓛_t` is `H`-strongly convex-concave with `H > 0`, it is the only saddle point.

**Formalization Note.** `IsSaddlePointOn X Y f a b` is Mathlib's `∀ x ∈ X, ∀ y ∈ Y, f a y ≤ f x b`,
the paper's (3); membership `a ∈ X`, `b ∈ Y` of the uniqueness clause is stated separately.
Convexity of `X` and `Y` is part of Mathlib's `ConvexOn`/`ConcaveOn` (inside `IsConvexConcaveOn`),
and nonemptiness is witnessed by `x 1 ∈ X`, `y 1 ∈ Y` in the run. `E`, `F` are arbitrary real
normed spaces. -/
theorem spftl_isSaddlePoint {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (X : Set E) (Y : Set F) (L : ℕ → E → F → ℝ) (G : ℝ) (T : ℕ) (x : ℕ → E) (y : ℕ → F)
    (hT : 1 ≤ T) (hX : IsCompact X) (hY : IsCompact Y)
    (hcc : ∀ t ∈ Finset.Icc 1 T, IsConvexConcaveOn X Y (L t))
    (hlip : ∀ t ∈ Finset.Icc 1 T, IsLipschitzPayoff X Y G (L t))
    (hrun : IsSPFTLRun L X Y T x y) :
    (∀ t ∈ Finset.Icc 1 T,
      IsSaddlePointOn X Y (cumPayoff L t) (x (t + 1)) (y (t + 1)) ∧
      cumPayoff L t (x (t + 1)) (y (t + 1)) = minimaxValue X Y (cumPayoff L t) ∧
      cumPayoff L t (x (t + 1)) (y (t + 1)) = maximinValue X Y (cumPayoff L t)) ∧
    (∀ H : ℝ, 0 < H → (∀ t ∈ Finset.Icc 1 T, IsStronglyConvexConcaveOn X Y H (L t)) →
      ∀ t ∈ Finset.Icc 1 T, ∀ a ∈ X, ∀ b ∈ Y,
        IsSaddlePointOn X Y (cumPayoff L t) a b → a = x (t + 1) ∧ b = y (t + 1)) := by sorry

end OnlineSaddlePoint
