-- Prove2me | Theorems.Thm_OnlineConvexOpt_OnlineBoosting_smoothed_regret_comparison_v2
-- name    : OnlineConvexOpt.OnlineBoosting.smoothed_regret_comparison_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:22:13.306843+00:00
-- url     : https://prove2.me/theorems/57cc6451-b41c-431f-bd49-efa2653d8854
-- title:
--   Lemma 12.5 — Stage-$N$ iterates of online boosting vs. the convex hull of $H$ (algorithm and WOCL guarantees explicit)
-- statement:
--   **Statement (Lemma 12.5).** Let $K\subseteq\mathbb R^n$ be convex with $0\in K$ and diameter at most $D$, $\gamma\in(0,1]$, $N,T\ge1$, and let $\hat f_1,\dots,\hat f_T:\mathbb R^n\to\mathbb R$ be convex, $\beta$-smooth (with gradient maps $\hat g_t=\nabla\hat f_t$) and $\hat G$-Lipschitz. Let $H\subseteq\{a\}\to K$ be a nonempty hypothesis class, and let the weak learners $W^1,\dots,W^N$ (predicting in $K$) drive Algorithm 36's inner recursion: $x^0_t=0$, $x^i_t=(1-\eta_i)x^{i-1}_t+\frac{\eta_i}\gamma W^i(a_t)$ with $\eta_i=\min\{2/i,1\}$, where $W^i$ is fed the linear stage loss $f^i_t(x)=\nabla\hat f_t(x^{i-1}_t)\cdot x$ and is a $\gamma$-WOCL for $H$ on these losses normalized by $\hat GD$ (so that their range on $K$ is $\le1$), with regret $\mathrm{Regret}_T(W)$. Then for every $h^\star\in\mathrm{CH}(H)$ (in particular the best hypothesis in the convex hull in hindsight) and $x^\star_t=h^\star(a_t)$,
--   $$\sum_{t=1}^{T}\hat f_t(x^N_t)-\sum_{t=1}^{T}\hat f_t(x^\star_t)\le\frac{2\beta D^2T}{\gamma^2N}+\frac{\hat GD}{\gamma}\mathrm{Regret}_T(W).$$
--
--   **Formalization Note.** The retired statement left $x^N$, $x^\star$ and $\mathrm{Regret}_T(W)$ as free variables, asserting a bare inequality between unrelated reals (refuted with $\mathrm{Regret}_T(W)=-10$). The new statement spells out Algorithm 36's inner recursion, identifies the stage losses with the gradients $\hat g_t(x^{i-1}_t)$, and assumes for each stage the WOCL guarantee (`IsGammaWOCL` of `OnlineConvexOpt_OnlineBoosting_WOCL_v2`, whose comparator is the real infimum over $H$) on the stage losses divided by $\hat GD$ — exactly the "equivalent restatement of the WOCL guarantee" the book's proof uses. Convexity of $\hat f_t$ (used in the proof's last inequality) and $\hat g_t$ being the gradient of $\hat f_t$ are explicit; $0\in K$ and $W^i(a_t)\in K$ give $\|\frac1\gamma W^i(a_t)-x^{i-1}_t\|\le D/\gamma$ as the proof needs; $h^\star$ ranges over all of $\mathrm{CH}(H)$ since the proof uses only $h^\star\in\mathrm{CH}(H)$. The recursion $\hat\Delta_i\le(1-\eta_i)\hat\Delta_{i-1}+\eta_i^2\beta D^2T/(2\gamma^2)$ with $\eta_1=1$ gives $\hat\Delta_N\le\frac{2\beta D^2T}{\gamma^2(N+1)}$ for every $N\ge1$ (Lemma 7.2 shifted by one index).
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 201, Lemma 12.5 (PDF p. 223)

import Mathlib
import Definitions.Def_OnlineConvexOpt_OnlineBoosting_SmoothOn
import Definitions.Def_OnlineConvexOpt_OnlineBoosting_WOCL_v2

namespace OnlineConvexOpt.OnlineBoosting

/-- Lemma 12.5 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 201, PDF p. 223). For smoothed loss functions `{f̂_t}` (convex on `ℝⁿ`,
`β`-smooth with gradient map `ĝ_t = ∇f̂_t`, and `Ĝ`-Lipschitz), the stage-`N` iterates of
Algorithm 36's inner recursion — `x^0_t = 0`, `x^i_t = (1-η_i)x^{i-1}_t + (η_i/γ)W^i(a_t)` with
`η_i = min{2/i, 1}`, the weak learners `W^i` being `γ`-WOCL for the stage losses
`f^i_t(x) = ∇f̂_t(x^{i-1}_t)·x` — satisfy, for every `h⋆` in the convex hull of `H` (in
particular the best hypothesis in hindsight) and `x⋆_t = h⋆(a_t)`,
`∑_{t=1}^T f̂_t(x^N_t) - ∑_{t=1}^T f̂_t(x⋆_t) ≤ (2βD²T)/(γ²N) + (ĜD/γ)Regret_T(W)`.

The WOCL guarantee is applied, as in the book's proof ("the following equivalent restatement of
the WOCL guarantee"), to the stage losses normalized by `ĜD` so that their range over `K` is at
most `1`, Definition 12.1's precondition. `K` is a convex set of diameter `≤ D` containing the
origin (the starting point `x^0_t = 0` of line 3), `H ⊆ {a} → K` is nonempty, and the weak
learners predict in `K`.

Corrected version: the retired statement left the iterates `x^N`, the comparator `x⋆` and
`Regret_T(W)` as unconstrained free variables, so it asserted a bare inequality between
unrelated reals; the inner recursion of Algorithm 36, the WOCL guarantees of the `W^i` (on the
normalized stage losses) and `h⋆ ∈ CH(H)` are now explicit hypotheses, together with the
convexity of `f̂_t` and the identification of `ĝ_t` with its gradient, both used in the proof. -/
theorem smoothed_regret_comparison_v2
    {n : ℕ} {A : Type*} (K : Set (EuclideanSpace ℝ (Fin n))) (hKconv : Convex ℝ K)
    (h0K : (0 : EuclideanSpace ℝ (Fin n)) ∈ K)
    (D γ : ℝ) (hDpos : 0 < D) (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (hγpos : 0 < γ) (hγ1 : γ ≤ 1)
    (N T : ℕ) (hN : 0 < N) (hT : 0 < T)
    (fhat : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (β Ghat : ℝ) (hβpos : 0 < β) (hGhatpos : 0 < Ghat)
    (ghat : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hghat : ∀ t x, HasGradientAt (fhat t) (ghat t x) x)
    (hfconv : ∀ t, ConvexOn ℝ Set.univ (fhat t))
    (hsmooth : ∀ t, SmoothOn Set.univ (fhat t) (ghat t) β)
    (hLip : ∀ t, ∀ x y, |fhat t x - fhat t y| ≤ Ghat * dist x y)
    (η : ℕ → ℝ) (hη : ∀ i : ℕ, 1 ≤ i → η i = min (2 / (i : ℝ)) 1)
    (a : ℕ → A) (H : Set (A → EuclideanSpace ℝ (Fin n))) (hHne : H.Nonempty)
    (hHK : ∀ h ∈ H, ∀ c : A, h c ∈ K)
    (W x : ℕ → ℕ → EuclideanSpace ℝ (Fin n)) (hW : ∀ t i, W t i ∈ K)
    (hx0 : ∀ t : ℕ, 1 ≤ t → t ≤ T → x t 0 = 0)
    (hxstep : ∀ t i : ℕ, 1 ≤ t → t ≤ T → 1 ≤ i → i ≤ N →
      x t i = (1 - η i) • x t (i - 1) + η i • ((1 / γ) • W t i))
    (fstage : ℕ → ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hfstage : ∀ t i : ℕ, 1 ≤ t → t ≤ T → 1 ≤ i → i ≤ N →
      fstage t i = fun y => inner ℝ (ghat t (x t (i - 1))) y)
    (RegretBoundW : ℝ)
    (hWOCL : ∀ i : ℕ, 1 ≤ i → i ≤ N →
      IsGammaWOCL K γ T a H (fun t => W t i) (fun t y => fstage t i y / (Ghat * D)) RegretBoundW)
    (hstar : A → EuclideanSpace ℝ (Fin n)) (hstar_mem : hstar ∈ convexHull ℝ H) :
    (∑ t ∈ Finset.Icc 1 T, fhat t (x t N)) - ∑ t ∈ Finset.Icc 1 T, fhat t (hstar (a t)) ≤
      (2 * β * D ^ 2 * T) / (γ ^ 2 * N) + (Ghat * D / γ) * RegretBoundW := by sorry

end OnlineConvexOpt.OnlineBoosting
