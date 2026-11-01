-- Prove2me | Theorems.Thm_MaxEntCont_theorem_5_6
-- name    : MaxEntCont.theorem_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:18:49.849128+00:00
-- url     : https://prove2.me/theorems/e6b5eea1-87ae-4f83-9eed-6b6a2ae88d33
-- title:
--   Theorem 5.6 — faces of $L=f(K)$ are lower semicontinuous along lifted sequences, and $\dim F(w)\le\liminf\dim F(w_i)$
-- statement:
--   Let $X,Y$ be finite-dimensional real normed spaces, $f:X\to Y$ linear, $K\subseteq X$ a convex body (compact and convex) and $L=f(K)$. For $u\in L$ let $F(u)$ be the face of $L$ containing $u$ in its relative interior, and write $\operatorname{ri}$ for the relative interior. Let $(w_i)_{i\in\mathbb N}\subseteq L$ converge to a point $w\in L$. Assume that
--
--   (a) the convex body $K$ is stable (the mid-point map $K\times K\to K$ is open), and
--
--   (b) a sequence $(v_i)_{i\in\mathbb N}\subseteq K$ converges to a point $v\in K$ such that $f(v_i)=w_i$ for all $i$, and $v$ lies in the relative interior of the fibre $f|_K^{-1}(w)=\{u\in K: f(u)=w\}$.
--
--   Then:
--
--   1. for every open subset $O$ of $L$ meeting $F(w)$ there is $N\in\mathbb N$ such that $O\cap F(w_i)\neq\emptyset$ for all $i\ge N$;
--   2. $$\dim F(w)\le\liminf_{i\to\infty}\dim F(w_i).$$
--
--   This is the main result of §5. In the quantum setting ($K$ the state space $\mathcal M_d$, which is stable, $f$ the expected-value map $\mathbb E$, and $v_i$ the maximum-entropy states) the hypotheses hold, and the theorem shows that the maximum-entropy inference $\rho^*$ is discontinuous at every point $w$ that is a limit of extremal points $w_i$ of $L$ but is not itself extremal.
--
--   **Formalization Note** $F(\cdot)$ is `minFace (f '' K) ·` (Fact 5.3), $\dim$ is `MaxEntCont.faceDim`, stability is `MaxEntCont.IsStable`, and the relative interior is `intrinsicInterior ℝ (K ∩ f ⁻¹' {w})`. The hypotheses $w\in L$, $w_i\in L$ and $w_i\to w$ of the source are kept although they follow from the others.
--
--   Differences from the source:
--   - reading: $\mathbb E(v_i)=w_i$ → `f (vs i) = ws i`; reason: the theorem is stated in the abstract setting of Def. 2.1 with the linear map $f$; $\mathbb E$ is the expected-value map (2.1), the paper's main example of $f$, and the proof uses the hypothesis as $f(F(v_i))\subseteq F(w_i)$ via Lemma 5.5(1)
--   - encoding: open subsets $O\subseteq L$ meeting $F(w)$ → open subsets $O$ of $Y$, intersected with $F(\cdot)$; reason: $F(\cdot)\subseteq L$, so $(O\cap L)\cap F(\cdot)=O\cap F(\cdot)$
--   - encoding: "there exists $N$ such that for all $i\ge N$" → `∀ᶠ i in atTop`; reason: the same statement
--   - encoding: $\liminf$ of natural numbers → `Filter.liminf` in `ℕ∞` of the cast values; reason: the same value, without Lean's junk value for an unbounded liminf in ℕ
--   - encoding: standing assumptions of pp. 4–5 (finite-dimensional real normed spaces, $K$ a convex body, $f$ linear) → explicit binders; reason: the paper's global assumptions, made explicit
--   - encoding: $F(\cdot)$, $\dim$ → `minFace`, `finrank ℝ (vectorSpan ℝ ·)`; reason: Fact 5.3 and the dimension of the affine hull
-- source:
--   Rodman, Spitkovsky, Szkoła, Weis, Continuity of the maximum-entropy inference, arXiv:1502.02018v1, Theorem 5.6, p. 14

import Mathlib
import Definitions.Def_TriangleFace
import Definitions.Def_MaxEntCont_faceDim
import Definitions.Def_MaxEntCont_IsStable

namespace MaxEntCont

open OAI.CanonicalFace198 Filter Topology

/-- **Theorem 5.6** (Rodman, Spitkovsky, Szkoła, Weis, *Continuity of the maximum-entropy inference*, arXiv:1502.02018v1, Theorem 5.6, p. 14): "Let `(wᵢ)_{i∈ℕ} ⊂ L` converge to a point `w ∈ L`.
We assume that (a) the convex body `K` is stable. We also assume that (b) a sequence
`(vᵢ)_{i∈ℕ} ⊂ K` converges to a point `v ∈ K` such that `𝔼(vᵢ) = wᵢ`, `i ∈ ℕ`, and such that `v`
lies in `ri(f|_K^{-1}(w))`. Then the following statements hold. (1) For all open subsets `O ⊂ L`
meeting `F(w)` there exists `N ∈ ℕ` such that for all `i ≥ N` we have `O ∩ F(wᵢ) ≠ ∅`. (2) We have
`dim F(w) ≤ lim inf_{i→∞} dim F(wᵢ)`."

Setting (p. 4–5): `X, Y` finite-dimensional real normed spaces, `K ⊆ X` a convex body (compact
and convex), `f : X → Y` linear, `L = f(K)`, `F(·)` the face function of `L`.

**Formalization Note**
* `𝔼(vᵢ) = wᵢ` is read as `f (vᵢ) = wᵢ`: the theorem is stated in the abstract setting of
  Def. 2.1, where the map is `f`; `𝔼` is the expected-value map of (2.1), the main example of `f`,
  and the proof uses the hypothesis as `f(F(vᵢ)) ⊂ F(wᵢ)` via Lemma 5.5(1).
* `F(w) = minFace (f '' K) w` (`MaxEntCont.fact_5_3`), `dim` is `MaxEntCont.faceDim` (dimension of
  the affine hull), stability is `MaxEntCont.IsStable` (mid-point map open, (5.2)).
* Open subsets of `L` (subspace topology) are traces `O ∩ L` of open `O ⊆ Y`; since `F(·) ⊆ L`,
  `(O ∩ L) ∩ F(·) = O ∩ F(·)`.
* `ri(f|_K^{-1}(w))` is `intrinsicInterior ℝ (K ∩ f⁻¹{w})`.
* "There exists `N` such that for all `i ≥ N`" is `∀ᶠ i in atTop`; the lim inf is taken in `ℕ∞`.
* The hypotheses `w ∈ L`, `wᵢ ∈ L` and `wᵢ → w` of the page are kept although they follow from
  the others. -/
theorem theorem_5_6 {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (K : Set X) (hKc : IsCompact K) (hKv : Convex ℝ K) (hK : IsStable K) (f : X →ₗ[ℝ] Y)
    (w : Y) (hw : w ∈ f '' K) (ws : ℕ → Y) (hws : ∀ i, ws i ∈ f '' K)
    (hlim : Tendsto ws atTop (𝓝 w))
    (v : X) (hv : v ∈ K) (vs : ℕ → X) (hvs : ∀ i, vs i ∈ K) (hvlim : Tendsto vs atTop (𝓝 v))
    (hfv : ∀ i, f (vs i) = ws i) (hri : v ∈ intrinsicInterior ℝ (K ∩ f ⁻¹' {w})) :
    (∀ O : Set Y, IsOpen O → (O ∩ minFace (f '' K) w).Nonempty →
        ∀ᶠ i in atTop, (O ∩ minFace (f '' K) (ws i)).Nonempty) ∧
      (faceDim (f '' K) w : ℕ∞) ≤
        Filter.liminf (fun i => (faceDim (f '' K) (ws i) : ℕ∞)) atTop := by sorry

end MaxEntCont
