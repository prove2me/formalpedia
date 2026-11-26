-- Prove2me | Theorems.Thm_OnlineSaddlePoint_Supplement_theorem_2
-- name    : OnlineSaddlePoint.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T21:54:08.024369+00:00
-- url     : https://prove2.me/theorems/3e6a2035-0d40-503f-be58-70c5f3b490e9
-- title:
--   Theorem 2 — SP-RFTL has SP-Regret $\le 8\eta[G_{\bar{\mathcal L}}+\frac1\eta\max(G_{R_X},G_{R_Y})]^2(1+\ln T)+\frac T\eta\max R_Y+\frac T\eta\max R_X$
-- statement:
--   Let $E$, $F$ be real normed spaces, $X\subseteq E$, $Y\subseteq F$ compact, $\eta>0$ and $T\in\mathbb N$. Let $\bar{\mathcal L}_1,\dots,\bar{\mathcal L}_T$ be convex-concave and $G_{\bar{\mathcal L}}$-Lipschitz on $X\times Y$. Let $R_X$, $R_Y$ be $1$-strongly convex on $X$, $Y$, Lipschitz there with constants $G_{R_X},G_{R_Y}\ge0$, and nonnegative on $X$, $Y$. Let $(x_t,y_t)_{t=1}^{T+1}$ be a run of SP-RFTL (Algorithm 2), that is, a run of Saddle-Point Follow-the-Leader on the regularized payoffs $\mathcal L_t=\bar{\mathcal L}_t+\frac1\eta R_X-\frac1\eta R_Y$. Then
--
--   $$
--   \left|\sum_{t=1}^T\bar{\mathcal L}_t(x_t,y_t)-\min_{x\in X}\max_{y\in Y}\sum_{t=1}^T\bar{\mathcal L}_t(x,y)\right|
--   \le 8\eta\Big[G_{\bar{\mathcal L}}+\frac1\eta\max(G_{R_X},G_{R_Y})\Big]^2(1+\ln T)+\frac T\eta\max_{y\in Y}R_Y(y)+\frac T\eta\max_{x\in X}R_X(x).
--   $$
--
--   This extends the logarithmic SP-Regret of SP-FTL (Theorem 1, the mission goal) from strongly convex-concave to arbitrary convex-concave Lipschitz games, at the price of the regularization terms; choosing $\eta$ of order $\sqrt T$ gives sublinear SP-Regret (Corollary 1), and Theorem 3 specializes it to matrix games.
--
--   Differences from the source:
--   - reading: SP-RFTL's update $\arg\min_{x\in X}\max_{y\in Y}\sum_{\tau=1}^t\mathcal L_t(x,y)$ (Algorithm 2) → an SP-FTL run (`IsSPFTLRun`) on $\mathcal L_\tau=\bar{\mathcal L}_\tau+\frac1\eta R_X-\frac1\eta R_Y$, i.e. $\sum_{\tau=1}^t\mathcal L_\tau$; reason: the summand index is a typo; p.14 says SP-RFTL runs SP-FTL on $\{\mathcal L_t\}$
--   - reading: the theorem's sentence does not repeat $R_X\ge0$ on $X$, $R_Y\ge0$ on $Y$ → both nonnegativity conditions are hypotheses; reason: assumed in the paragraph before the theorem (\"Finally, we assume $R_X(x)\ge0$ for all $x\in X$ and $R_Y(y)\ge0$ for all $y\in Y$\", p.11) and used through Lemma 3
--   - reading: $R_X$, $R_Y$ "strongly convex" with no modulus stated (p.11; p.5 defines $H$-strong convexity) → modulus $1$ (`StrongConvexOn X 1 RX`, `StrongConvexOn Y 1 RY`); reason: the proof (p.12) uses that $\mathcal L_t$ is $\frac1\eta$-strongly convex-concave, which needs modulus $1$; with a smaller modulus the stated bound fails (as the modulus tends to $0$ SP-RFTL approaches unregularized SP-FTL), and a modulus $\ge1$ implies modulus $1$
--   - generalization: $X\subset\mathbb R^{d_1}$, $Y\subset\mathbb R^{d_2}$ with any norm → $X$, $Y$ subsets of arbitrary real normed spaces $E$, $F$; reason: $\mathbb R^{d}$ with any norm is a real normed space, and no finite dimension is used
--   - generalization: $|\bar{\mathcal L}(x_1,y_1)-\bar{\mathcal L}(x_2,y_2)|\le G_{\bar{\mathcal L}}\|[x_1;y_1]-[x_2;y_2]\|$ → $|\bar{\mathcal L}(x_1,y_1)-\bar{\mathcal L}(x_2,y_2)|\le G_{\bar{\mathcal L}}(\|x_1-x_2\|+\|y_1-y_2\|)$ on $X\times Y$, with $G_{\bar{\mathcal L}}\ge0$; reason: implied by the paper's form for every stacked norm with $\|[a;b]\|\le\|a\|+\|b\|$; it is the form the proofs on pp.7, 9, 10, 14 use; a Lipschitz constant is nonnegative
--   - generalization: $R_X$, $R_Y$ strongly convex with respect to $\|\cdot\|$ (subgradient form of p.5) → Mathlib `StrongConvexOn X 1 RX`, `StrongConvexOn Y 1 RY` (chord inequality with modulus $\frac12 r^2$); reason: the subgradient form implies the chord form, so the hypothesis is weaker; the modulus $1$ is the one the proof on p.12 uses ($\mathcal L_t$ is $\frac1\eta$-strongly convex-concave)
--   - generalization: $G_{R_X}$-Lipschitz meaning $\|\nabla R_X(x)\|_*\le G_{R_X}$ for all $x\in X$ (p.11) → $|R_X(a)-R_X(b)|\le G_{R_X}\|a-b\|$ for $a,b\in X$, with $G_{R_X}\ge0$ (likewise for $R_Y$); reason: on the convex set $X$ the gradient bound implies this Lipschitz bound, so the hypothesis is weaker
--   - encoding: $\bar{\mathcal L}_t : X\times Y\to\mathbb R$, $R_X : X\to\mathbb R$, $R_Y : Y\to\mathbb R$ → functions on all of $E\times F$, $E$, $F$; only their values on $X\times Y$, $X$, $Y$ enter; reason: a function on $X\times Y$ extends arbitrarily; no hypothesis or conclusion reads values outside
--   - encoding: $\min_{x\in X}\max_{y\in Y}$, $\max_{x\in X}R_X(x)$, $\arg\min$, $\arg\max$ → `sInf`/`sSup` of images in $\mathbb R$; arg min/arg max memberships written as `sSup`/`sInf` inequalities; reason: under compactness and continuity the extrema are attained, so `sInf`/`sSup` are the paper's min/max
--   - encoding: $X$, $Y$ convex (and nonempty) → convexity carried by `StrongConvexOn` of the regularizers (which includes convexity of the set); nonemptiness by a given point of $X$ and of $Y$; reason: the same instances
--   - encoding: $\ln(T)$ → `Real.log T`; reason: the natural logarithm
--   - generalization: $t=1,\dots,T$ (implicitly $T\ge1$) → any $T\in\mathbb N$; reason: at $T=0$ the SP-Regret is $0$ and the bound is $8\eta G^2\ge0$, so the statement specializes to the source for $T\ge1$
-- source:
--   Rivera Cardoso, Wang, Xu, The Online Saddle Point Problem and Online Convex Optimization with Knapsacks, arXiv:1806.08301v3, Theorem 2, p.11 (proof pp.12–15); standing assumptions §4.2, p.11

import Mathlib
import Definitions.Def_OnlineSaddlePoint_spRegret
import Definitions.Def_OnlineSaddlePoint_IsConvexConcaveOn
import Definitions.Def_OnlineSaddlePoint_IsLipschitzPayoff
import Definitions.Def_OnlineSaddlePoint_IsSPFTLRun
import Definitions.Def_OnlineSaddlePoint_Supplement_regularizedPayoff

namespace OnlineSaddlePoint.Supplement

open OnlineSaddlePoint

/-- **Theorem 2 (SP-RFTL on general convex-concave games).** Rivera Cardoso, Wang, Xu,
arXiv:1806.08301v3, Theorem 2, p.11: "Let `X ⊂ ℝ^{d₁}` and `Y ⊂ ℝ^{d₂}` be convex and compact sets.
Let `{𝓛̄_t(x, y)}_{t=1}^T` be any sequence of convex-concave functions. For `t = 1, ..., T`, let `𝓛̄_t`
be `G_𝓛̄`-Lipschitz with respect to norm `‖·‖`. Let `R_X`, `R_Y` be two strongly convex regularization
functions with respect to the same norm, and let `G_{R_X}`, `G_{R_Y}` be the Lipschitz constants of
`R_X`, `R_Y`. Let `{(x_t, y_t)}_{t=1}^T` be the iterates generated by SP-RFTL when run on the sequence
`{𝓛̄_t(x, y)}_{t=1}^T`. It holds that
`|∑_{t=1}^T 𝓛̄_t(x_t, y_t) − min_{x∈X} max_{y∈Y} ∑_{t=1}^T 𝓛̄_t(x, y)|
≤ 8η [G_𝓛̄ + (1/η) max(G_{R_X}, G_{R_Y})]² (1 + ln(T)) + (T/η) max_{y∈Y} R_Y(y) + (T/η) max_{x∈X} R_X(x)`,
where `η > 0` is the parameter chosen in Algorithm 2."

**Formalization Note.** An SP-RFTL run (Algorithm 2) is an SP-FTL run (`IsSPFTLRun`) on
`regularizedPayoff Lbar RX RY η`; the regret is the SP-Regret (`spRegret`) of the unregularized
`𝓛̄_t` along its iterates. The §4.2 standing assumption `R_X ≥ 0` on `X`, `R_Y ≥ 0` on `Y` (p.11) is a
hypothesis. "Strongly convex" is `StrongConvexOn _ 1` (modulus `1`: the proof on p.12 uses that
`𝓛_t` is `1/η`-strongly convex-concave). Lipschitz conditions are stated on `X`, `Y`; for `𝓛̄_t` it is
`IsLipschitzPayoff` (sum-of-norms form, implied by the paper's). `ℝ^{d₁}`, `ℝ^{d₂}` with any norm are
arbitrary real normed spaces. `ln` is `Real.log`; `max_{x∈X} R_X(x)` is `sSup (RX '' X)` (attained,
`R_X` being continuous on the compact `X`). The bound is on the absolute value: both directions. -/
theorem theorem_2 {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (X : Set E) (Y : Set F) (Lbar : ℕ → E → F → ℝ) (RX : E → ℝ) (RY : F → ℝ)
    (η Gbar GRX GRY : ℝ) (T : ℕ) (x : ℕ → E) (y : ℕ → F)
    (hX : IsCompact X) (hY : IsCompact Y) (hη : 0 < η)
    (hcc : ∀ t ∈ Finset.Icc 1 T, IsConvexConcaveOn X Y (Lbar t))
    (hlip : ∀ t ∈ Finset.Icc 1 T, IsLipschitzPayoff X Y Gbar (Lbar t))
    (hRXsc : StrongConvexOn X 1 RX) (hRYsc : StrongConvexOn Y 1 RY)
    (hRXlip : 0 ≤ GRX ∧ ∀ a ∈ X, ∀ b ∈ X, |RX a - RX b| ≤ GRX * ‖a - b‖)
    (hRYlip : 0 ≤ GRY ∧ ∀ a ∈ Y, ∀ b ∈ Y, |RY a - RY b| ≤ GRY * ‖a - b‖)
    (hRXnn : ∀ a ∈ X, 0 ≤ RX a) (hRYnn : ∀ b ∈ Y, 0 ≤ RY b)
    (hrun : IsSPFTLRun (regularizedPayoff Lbar RX RY η) X Y T x y) :
    spRegret Lbar X Y T x y ≤
      8 * η * (Gbar + 1 / η * max GRX GRY) ^ 2 * (1 + Real.log T) +
        (T : ℝ) / η * sSup (RY '' Y) + (T : ℝ) / η * sSup (RX '' X) := by sorry

end OnlineSaddlePoint.Supplement
