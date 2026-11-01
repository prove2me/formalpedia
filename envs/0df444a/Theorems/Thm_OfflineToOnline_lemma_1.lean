-- Prove2me | Theorems.Thm_OfflineToOnline_lemma_1
-- name    : OfflineToOnline.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:34:36.183315+00:00
-- url     : https://prove2.me/theorems/b016320c-345e-455d-8edf-3ca4e05d863c
-- title:
--   Lemma 1 — the Blackwell-to-OLO conversion, in $d_2$ (as printed) and in $d_\infty$
-- statement:
--   Let $(\mathcal X,\mathcal Y,\boldsymbol p)$ be a Blackwell game ($\mathcal X,\mathcal Y$ compact and convex, $\mathcal X$ nonempty, $\boldsymbol p$ biaffine) and let $S\subseteq\mathbb R^d$ be a nonempty closed convex cone that is response-satisfiable. Then:
--
--   1. **Conversion.** There is a map $\varphi$ from OLO decisions to player 1 actions such that for every $w\in S^\circ$, $\varphi(w)\in\mathcal X$ and $\langle w,\boldsymbol p(\varphi(w),y)\rangle\le0$ for all $y\in\mathcal Y$; that is, $\boldsymbol p(\varphi(w),y)$ lies in the halfspace $H_w=\{x:\langle w,x\rangle\le0\}\supseteq S$.
--   2. **Bound.** For every such $\varphi$, every $T\ge1$, every $y_1,\dots,y_T\in\mathcal Y$ and every $w_1,\dots,w_T\in S^\circ$, with $x_t=\varphi(w_t)$ and $l_t=-\boldsymbol p(x_t,y_t)$,
--
--   $$
--   d_2\Big(\frac1T\sum_{t=1}^T\boldsymbol p(x_t,y_t),S\Big)\le\frac1T\Big(\sum_{t=1}^T\langle l_t,w_t\rangle-\min_{w\in S^\circ\cap B_2(1)}\sum_{t=1}^T\langle l_t,w\rangle\Big)
--   $$
--
--   and
--
--   $$
--   d_\infty\Big(\frac1T\sum_{t=1}^T\boldsymbol p(x_t,y_t),S\Big)\le\frac1T\Big(\sum_{t=1}^T\langle l_t,w_t\rangle-\min_{w\in S^\circ\cap B_1(1)}\sum_{t=1}^T\langle l_t,w\rangle\Big).
--   $$
--
--   So any online linear optimization algorithm on $K=S^\circ\cap B_2(1)$ (respectively $S^\circ\cap B_1(1)$) with small regret yields a player 1 strategy that approaches $S$ in $d_2$ (respectively $d_\infty$). The $d_\infty$ form is what the $\ell_\infty$ rate of Theorem 1 needs.
--
--   Differences from the source:
--   - reading: the OLO decision w_t can be converted into x_t ∈ X → there is a map φ with φ(w) ∈ X and ⟨w, p(φ(w), y)⟩ ≤ 0 for all w ∈ S°, y ∈ Y, and x_t = φ(w_t); reason: this is the halfspace-oracle conversion described in the proof on p.46
--   - generalization: decisions w_t ∈ K = S° ∩ B₂(1) returned by the OLO algorithm → any w_t ∈ S°, and every conversion φ with the halfspace property; reason: the bound holds for these; decisions in K and the paper's conversion are special cases
--   - generalization: the d₂ bound with K = S° ∩ B₂(1) → the d₂ bound and, in addition, the d∞ bound with S° ∩ B₁(1); reason: the extra conjunct is the ℓ∞ form needed by Theorem 1; the d₂ conjunct is the printed statement
--   - encoding: a cone S that is response-satisfiable (Definition 4: closed and convex) → a nonempty closed convex set closed under nonnegative scaling; X nonempty; reason: Metric.infDist to ∅ is 0; a game needs a player 1 action
--   - encoding: min over K; rounds t = 1..T → sInf of the image of the compact set K (it contains 0); rounds 0..T−1; reason: the minimum exists, so sInf equals it
-- source:
--   Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, Online Learning via Offline Greedy Algorithms: Applications in Market Design and Optimization, arXiv:2102.11050v4, Lemma 1, p.46 (with its proof and (5), p.46)

import Mathlib
import Definitions.Def_OfflineToOnline_IsBiaffineOn
import Definitions.Def_OfflineToOnline_IsResponseSatisfiable
import Definitions.Def_OfflineToOnline_polarCone
import Definitions.Def_OfflineToOnline_l2InfDist

namespace OfflineToOnline

/-- **Lemma 1** (Abernethy et al. 2011), with the ℓ∞ form used in the proof of Theorem 1. Let
`(X, Y, p)` be a Blackwell game (`X`, `Y` compact convex, `X` nonempty, `p` biaffine) and `S` a
nonempty closed convex cone that is response-satisfiable. Then:

1. there is a conversion `φ` from OLO decisions to player 1 actions: for every `w ∈ S°`,
   `φ(w) ∈ X` and `⟨w, p(φ(w), y)⟩ ≤ 0` for all `y ∈ Y` (`p(φ(w), y)` lies in the halfspace
   `H_w = {x : ⟨w, x⟩ ≤ 0} ⊇ S`);
2. for every such `φ`, every `T ≥ 1`, every `y_1, …, y_T ∈ Y` and OLO decisions
   `w_1, …, w_T ∈ S°`, with `x_t = φ(w_t)` and `l_t = −p(x_t, y_t)`:
   (a) `d₂((1/T) ∑_t p(x_t, y_t), S) ≤ (1/T)(∑_t ⟨l_t, w_t⟩ − min_{w ∈ S° ∩ B₂(1)} ∑_t ⟨l_t, w⟩)`;
   (b) `d∞((1/T) ∑_t p(x_t, y_t), S) ≤ (1/T)(∑_t ⟨l_t, w_t⟩ − min_{w ∈ S° ∩ B₁(1)} ∑_t ⟨l_t, w⟩)`.

Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, arXiv:2102.11050v4, Lemma 1, p.46 (statement and its proof, (5); the halfspace oracle, p.46).

Formalization Note: rounds are `0, …, T − 1`. The minima over the compact sets `S° ∩ B₂(1)` and
`S° ∩ B₁(1)` (which contain `0`) are written as `sInf` of the image. `d₂` is `l2InfDist`, `d∞` is
`Metric.infDist` in `Fin d → ℝ`. Part (b) is the ℓ∞ version with the ℓ1 ball (the dual norm of
ℓ∞). The decisions `w_t` are only required to lie in `S°`, not in the ball. -/
theorem lemma_1 {m k d : ℕ} (X : Set (Fin m → ℝ)) (Y : Set (Fin k → ℝ))
    (p : (Fin m → ℝ) → (Fin k → ℝ) → (Fin d → ℝ)) (S : Set (Fin d → ℝ))
    (hXc : IsCompact X) (hXv : Convex ℝ X) (hXn : X.Nonempty) (hYc : IsCompact Y)
    (hYv : Convex ℝ Y) (hp : IsBiaffineOn X Y p) (hSc : IsClosed S) (hSv : Convex ℝ S)
    (hScone : ∀ s ∈ S, ∀ a : ℝ, 0 ≤ a → a • s ∈ S) (hSn : S.Nonempty)
    (hrs : IsResponseSatisfiable X Y p S) :
    (∃ φ : (Fin d → ℝ) → Fin m → ℝ,
        ∀ w ∈ polarCone S, φ w ∈ X ∧ ∀ y ∈ Y, ∑ j, w j * p (φ w) y j ≤ 0) ∧
      ∀ φ : (Fin d → ℝ) → Fin m → ℝ,
        (∀ w ∈ polarCone S, φ w ∈ X ∧ ∀ y ∈ Y, ∑ j, w j * p (φ w) y j ≤ 0) →
        ∀ T : ℕ, 1 ≤ T → ∀ y : ℕ → Fin k → ℝ, (∀ t < T, y t ∈ Y) →
        ∀ w : ℕ → Fin d → ℝ, (∀ t < T, w t ∈ polarCone S) →
          l2InfDist ((T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, p (φ (w t)) (y t)) S ≤
              (T : ℝ)⁻¹ * (∑ t ∈ Finset.range T, ∑ j, -p (φ (w t)) (y t) j * w t j -
                sInf ((fun v : Fin d → ℝ => ∑ t ∈ Finset.range T, ∑ j, -p (φ (w t)) (y t) j * v j) ''
                  (polarCone S ∩ {v | ∑ j, v j ^ 2 ≤ 1}))) ∧
            Metric.infDist ((T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, p (φ (w t)) (y t)) S ≤
              (T : ℝ)⁻¹ * (∑ t ∈ Finset.range T, ∑ j, -p (φ (w t)) (y t) j * w t j -
                sInf ((fun v : Fin d → ℝ => ∑ t ∈ Finset.range T, ∑ j, -p (φ (w t)) (y t) j * v j) ''
                  (polarCone S ∩ {v | ∑ j, |v j| ≤ 1}))) := by sorry

end OfflineToOnline
