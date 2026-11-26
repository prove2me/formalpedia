-- Prove2me | Theorems.Thm_OnlineSaddlePoint_Supplement_lemma_3
-- name    : OnlineSaddlePoint.Supplement.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T21:53:31.865669+00:00
-- url     : https://prove2.me/theorems/718fb2e5-06da-5cf3-a9a5-85ba3eb50ab8
-- title:
--   Lemma 3 — regularized and unregularized game values differ by at most $\frac T\eta R_X(\bar x_{T+1})$ above and $\frac T\eta R_Y(\bar y_{T+1})$ below
-- statement:
--   Let $E$, $F$ be real normed spaces, $X\subseteq E$, $Y\subseteq F$ compact, $\eta>0$ and $T\in\mathbb N$. Let $\bar{\mathcal L}_1,\dots,\bar{\mathcal L}_T$ be convex-concave and $G_{\bar{\mathcal L}}$-Lipschitz on $X\times Y$, and let $R_X$, $R_Y$ be $1$-strongly convex, Lipschitz (with constants $G_{R_X},G_{R_Y}\ge0$) and nonnegative on $X$, $Y$ respectively. Put
--
--   $$
--   \mathcal L_t(x,y)=\bar{\mathcal L}_t(x,y)+\frac1\eta R_X(x)-\frac1\eta R_Y(y).
--   $$
--
--   Let $\bar x_{T+1}\in X$ minimize $x\mapsto\max_{y\in Y}\sum_{t=1}^T\bar{\mathcal L}_t(x,y)$ over $X$, and $\bar y_{T+1}\in Y$ maximize $y\mapsto\min_{x\in X}\sum_{t=1}^T\bar{\mathcal L}_t(x,y)$ over $Y$. Then
--
--   $$
--   -\frac T\eta R_Y(\bar y_{T+1})\ \le\ \min_{x\in X}\max_{y\in Y}\sum_{t=1}^T\mathcal L_t(x,y)-\min_{x\in X}\max_{y\in Y}\sum_{t=1}^T\bar{\mathcal L}_t(x,y)\ \le\ \frac T\eta R_X(\bar x_{T+1}).
--   $$
--
--   The lemma measures how much the regularization moves the value of the cumulative game; in the proof of Theorem 2 it converts the SP-Regret of SP-FTL on the regularized games into a bound for the original games.
--
--   Differences from the source:
--   - reading: Lemma 3 says "$\{\mathcal L_t\}_{t=1}^T$ be any sequence of convex-concave functions" → convex-concavity is assumed of the observed $\bar{\mathcal L}_t$, and $\mathcal L_t=\bar{\mathcal L}_t+\frac1\eta R_X-\frac1\eta R_Y$; reason: the conclusion is about $\bar{\mathcal L}_t$ and the regularized $\mathcal L_t$ defined on p.12, and the proof uses that $\sum\bar{\mathcal L}_t$ has a saddle point; with $R_X$, $R_Y$ convex, $\mathcal L_t$ is then convex-concave too
--   - reading: the lemma's sentence lists only convexity and compactness → the §4.2 standing assumptions are hypotheses: $\bar{\mathcal L}_t$ $G_{\bar{\mathcal L}}$-Lipschitz, $R_X$, $R_Y$ strongly convex, Lipschitz and nonnegative, $\eta>0$; reason: §4.2 (p.11) states them for the whole section; nonnegativity is used on p.13, and the Lipschitz bounds give the continuity that makes the saddle points of the proof exist
--   - reading: $R_X$, $R_Y$ "strongly convex" with no modulus stated (p.11; p.5 defines $H$-strong convexity) → modulus $1$ (`StrongConvexOn X 1 RX`, `StrongConvexOn Y 1 RY`); reason: the proof (p.12) uses that $\mathcal L_t$ is $\frac1\eta$-strongly convex-concave, which needs modulus $1$; with a smaller modulus the stated bound fails (as the modulus tends to $0$ SP-RFTL approaches unregularized SP-FTL), and a modulus $\ge1$ implies modulus $1$
--   - generalization: $X\subset\mathbb R^{d_1}$, $Y\subset\mathbb R^{d_2}$ with any norm → $X$, $Y$ subsets of arbitrary real normed spaces $E$, $F$; reason: $\mathbb R^{d}$ with any norm is a real normed space, and no finite dimension is used
--   - generalization: $|\bar{\mathcal L}(x_1,y_1)-\bar{\mathcal L}(x_2,y_2)|\le G_{\bar{\mathcal L}}\|[x_1;y_1]-[x_2;y_2]\|$ → $|\bar{\mathcal L}(x_1,y_1)-\bar{\mathcal L}(x_2,y_2)|\le G_{\bar{\mathcal L}}(\|x_1-x_2\|+\|y_1-y_2\|)$ on $X\times Y$, with $G_{\bar{\mathcal L}}\ge0$; reason: implied by the paper's form for every stacked norm with $\|[a;b]\|\le\|a\|+\|b\|$; it is the form the proofs on pp.7, 9, 10, 14 use; a Lipschitz constant is nonnegative
--   - generalization: $R_X$, $R_Y$ strongly convex with respect to $\|\cdot\|$ (subgradient form of p.5) → Mathlib `StrongConvexOn X 1 RX`, `StrongConvexOn Y 1 RY` (chord inequality with modulus $\frac12 r^2$); reason: the subgradient form implies the chord form, so the hypothesis is weaker; the modulus $1$ is the one the proof on p.12 uses ($\mathcal L_t$ is $\frac1\eta$-strongly convex-concave)
--   - generalization: $G_{R_X}$-Lipschitz meaning $\|\nabla R_X(x)\|_*\le G_{R_X}$ for all $x\in X$ (p.11) → $|R_X(a)-R_X(b)|\le G_{R_X}\|a-b\|$ for $a,b\in X$, with $G_{R_X}\ge0$ (likewise for $R_Y$); reason: on the convex set $X$ the gradient bound implies this Lipschitz bound, so the hypothesis is weaker
--   - encoding: $\bar{\mathcal L}_t : X\times Y\to\mathbb R$, $R_X : X\to\mathbb R$, $R_Y : Y\to\mathbb R$ → functions on all of $E\times F$, $E$, $F$; only their values on $X\times Y$, $X$, $Y$ enter; reason: a function on $X\times Y$ extends arbitrarily; no hypothesis or conclusion reads values outside
--   - encoding: $\min_{x\in X}\max_{y\in Y}$, $\max_{x\in X}R_X(x)$, $\arg\min$, $\arg\max$ → `sInf`/`sSup` of images in $\mathbb R$; arg min/arg max memberships written as `sSup`/`sInf` inequalities; reason: under compactness and continuity the extrema are attained, so `sInf`/`sSup` are the paper's min/max
--   - encoding: $X$, $Y$ convex (and nonempty) → convexity carried by `StrongConvexOn` of the regularizers (which includes convexity of the set); nonemptiness by a given point of $X$ and of $Y$; reason: the same instances
--   - generalization: $t=1,\dots,T$ (implicitly $T\ge1$) → any $T\in\mathbb N$; reason: at $T=0$ both values are $0$ and both bounds are $0$, so the statement specializes to the source for $T\ge1$
-- source:
--   Rivera Cardoso, Wang, Xu, The Online Saddle Point Problem and Online Convex Optimization with Knapsacks, arXiv:1806.08301v3, Lemma 3, p.12 (proof p.13–14); standing assumptions §4.2, p.11

import Mathlib
import Definitions.Def_OnlineSaddlePoint_cumPayoff
import Definitions.Def_OnlineSaddlePoint_minimaxValue
import Definitions.Def_OnlineSaddlePoint_IsConvexConcaveOn
import Definitions.Def_OnlineSaddlePoint_IsLipschitzPayoff
import Definitions.Def_OnlineSaddlePoint_Supplement_regularizedPayoff

namespace OnlineSaddlePoint.Supplement

open OnlineSaddlePoint

/-- **Lemma 3 (regularized vs unregularized game value).** Rivera Cardoso, Wang, Xu,
arXiv:1806.08301v3, Lemma 3, p.12: "Let `X ⊆ ℝ^{d₁}`, `Y ⊆ ℝ^{d₂}` be convex and compact sets. Let
`{𝓛_t}_{t=1}^T` be any sequence of convex-concave functions where `𝓛_t : X × Y → ℝ` for all
`t = 1, ..., T`. Let `x̄_{T+1} ∈ arg min_{x∈X} max_{y∈Y} ∑_{t=1}^T 𝓛̄_t(x, y)`,
`ȳ_{T+1} ∈ arg max_{y∈Y} min_{x∈X} ∑_{t=1}^T 𝓛̄_t(x, y)`. It holds that
`−(T/η) R_Y(ȳ_{T+1}) ≤ min_{x∈X} max_{y∈Y} ∑_{t=1}^T 𝓛_t(x, y) − min_{x∈X} max_{y∈Y} ∑_{t=1}^T 𝓛̄_t(x, y)
≤ (T/η) R_X(x̄_{T+1})`."

Here `𝓛_t = 𝓛̄_t + (1/η)R_X − (1/η)R_Y` (p.12), and the standing assumptions of §4.2 (p.11) hold:
each `𝓛̄_t` is convex-concave and `G_𝓛̄`-Lipschitz, `R_X`, `R_Y` are strongly convex (modulus `1`),
Lipschitz and nonnegative on `X`, `Y`, and `η > 0`.

**Formalization Note.** The printed "`{𝓛_t}` be any sequence of convex-concave functions" is read as
the observed `𝓛̄_t`: the conclusion is about `𝓛̄_t` and the regularized `𝓛_t`, and the proof (p.13)
uses that `∑ 𝓛̄_t` has a saddle point. `ℝ^{d₁}`, `ℝ^{d₂}` with any norm are arbitrary real normed
spaces. "Strongly convex" is Mathlib's `StrongConvexOn _ 1` (the proof of Theorem 2 on p.12 uses that
`𝓛_t` is `1/η`-strongly convex-concave). The regularizers' Lipschitz condition is stated on `X`
(`|R(a) − R(b)| ≤ G_R ‖a − b‖`), implied by the paper's `‖∇R‖_* ≤ G_R` on the convex set. The
arg min/arg max memberships are written out with `sSup`/`sInf` exactly as in `IsSPFTLRun`.
Convexity of `X`, `Y` is carried by `StrongConvexOn`; nonemptiness by `x̄ ∈ X`, `ȳ ∈ Y`. -/
theorem lemma_3 {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (X : Set E) (Y : Set F) (Lbar : ℕ → E → F → ℝ) (RX : E → ℝ) (RY : F → ℝ)
    (η Gbar GRX GRY : ℝ) (T : ℕ) (xbar : E) (ybar : F)
    (hX : IsCompact X) (hY : IsCompact Y) (hη : 0 < η)
    (hcc : ∀ t ∈ Finset.Icc 1 T, IsConvexConcaveOn X Y (Lbar t))
    (hlip : ∀ t ∈ Finset.Icc 1 T, IsLipschitzPayoff X Y Gbar (Lbar t))
    (hRXsc : StrongConvexOn X 1 RX) (hRYsc : StrongConvexOn Y 1 RY)
    (hRXlip : 0 ≤ GRX ∧ ∀ a ∈ X, ∀ b ∈ X, |RX a - RX b| ≤ GRX * ‖a - b‖)
    (hRYlip : 0 ≤ GRY ∧ ∀ a ∈ Y, ∀ b ∈ Y, |RY a - RY b| ≤ GRY * ‖a - b‖)
    (hRXnn : ∀ a ∈ X, 0 ≤ RX a) (hRYnn : ∀ b ∈ Y, 0 ≤ RY b)
    (hxbar : xbar ∈ X ∧ ∀ x' ∈ X, sSup ((fun y' => cumPayoff Lbar T xbar y') '' Y) ≤
      sSup ((fun y' => cumPayoff Lbar T x' y') '' Y))
    (hybar : ybar ∈ Y ∧ ∀ y' ∈ Y, sInf ((fun x' => cumPayoff Lbar T x' y') '' X) ≤
      sInf ((fun x' => cumPayoff Lbar T x' ybar) '' X)) :
    -((T : ℝ) / η * RY ybar) ≤
        minimaxValue X Y (cumPayoff (regularizedPayoff Lbar RX RY η) T) -
          minimaxValue X Y (cumPayoff Lbar T) ∧
      minimaxValue X Y (cumPayoff (regularizedPayoff Lbar RX RY η) T) -
          minimaxValue X Y (cumPayoff Lbar T) ≤ (T : ℝ) / η * RX xbar := by sorry

end OnlineSaddlePoint.Supplement
