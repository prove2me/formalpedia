-- Prove2me | Theorems.Thm_OnlineSaddlePoint_lemma_2
-- name    : OnlineSaddlePoint.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:14:14.619207+00:00
-- url     : https://prove2.me/theorems/fd27e59f-80c0-4e13-9ed4-070b2348ab53
-- title:
--   Lemma 2 — consecutive SP-FTL iterates are within $4G/(Ht)$
-- statement:
--   Let $E$, $F$ be real normed spaces, $X\subseteq E$, $Y\subseteq F$ compact, $T\ge1$, $H>0$, and let $\mathcal L_1,\dots,\mathcal L_T$ be $H$-strongly convex-concave and $G$-Lipschitz on $X\times Y$. Let $(x_t,y_t)_{t=1}^{T+1}$ be a run of Saddle-Point Follow-the-Leader. Then for every $t=1,\dots,T$
--
--   $$
--   \|x_t-x_{t+1}\|+\|y_t-y_{t+1}\|\le\frac{4G}{Ht}.
--   $$
--
--   The bound holds at $t=1$ as well, whatever the starting point $(x_1,y_1)\in X\times Y$. Summed over $t$ it gives the harmonic series, which is where the logarithm in Theorem 1 comes from.
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
-- source:
--   Rivera Cardoso, Wang, Xu, The Online Saddle Point Problem and Online Convex Optimization with Knapsacks, arXiv:1806.08301v3, Lemma 2, p.8

import Mathlib
import Definitions.Def_OnlineSaddlePoint_IsStronglyConvexConcaveOn
import Definitions.Def_OnlineSaddlePoint_IsLipschitzPayoff
import Definitions.Def_OnlineSaddlePoint_IsSPFTLRun

namespace OnlineSaddlePoint

/-- **Lemma 2 (consecutive SP-FTL iterates are `O(1/t)` apart).** Rivera Cardoso, Wang, Xu,
arXiv:1806.08301v3, Lemma 2, p.8: "Let `{𝓛_t}_{t=1}^T` be an arbitrary sequence of `H`-strongly
convex-concave functions (with respect to norm `‖·‖`) which is also `G`-Lipschitz with respect to
the same norm. Let `{(x_t, y_t)}_{t=1}^T` be the iterates of SP-FTL run on the sequence
`{𝓛_t}_{t=1}^T`. It holds that `‖x_t − x_{t+1}‖ + ‖y_t − y_{t+1}‖ ≤ 4G/(Ht)`."

**Formalization Note.** The bound is stated for every round `t = 1, …, T`, including `t = 1`, where
`x₁ ∈ X`, `y₁ ∈ Y` are the arbitrary inputs. `E`, `F` are arbitrary real normed spaces;
`H`-strong convexity/concavity is Mathlib's `StrongConvexOn`/`StrongConcaveOn` (implied by the
paper's subgradient definition); `H > 0` is the paper's "strongly". `X`, `Y` are compact, as in
the paper's standing assumptions (p.1, Lemma 1); their convexity is part of `StrongConvexOn`. -/
theorem lemma_2 {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (X : Set E) (Y : Set F) (L : ℕ → E → F → ℝ) (H G : ℝ) (T : ℕ) (x : ℕ → E) (y : ℕ → F)
    (hT : 1 ≤ T) (hX : IsCompact X) (hY : IsCompact Y) (hH : 0 < H)
    (hsc : ∀ t ∈ Finset.Icc 1 T, IsStronglyConvexConcaveOn X Y H (L t))
    (hlip : ∀ t ∈ Finset.Icc 1 T, IsLipschitzPayoff X Y G (L t))
    (hrun : IsSPFTLRun L X Y T x y) :
    ∀ t ∈ Finset.Icc 1 T, ‖x t - x (t + 1)‖ + ‖y t - y (t + 1)‖ ≤ 4 * G / (H * t) := by sorry

end OnlineSaddlePoint
