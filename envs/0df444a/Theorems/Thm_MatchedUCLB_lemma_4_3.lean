-- Prove2me | Theorems.Thm_MatchedUCLB_lemma_4_3
-- name    : MatchedUCLB.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:34:23.693293+00:00
-- url     : https://prove2.me/theorems/291d6e6e-3b85-4d0c-a494-ec7728916161
-- title:
--   Lemma 4.3 — the uniformly convex base $B$: smoothness, Bregman growth, center values and exact local formulas
-- statement:
--   Let $q=p+\nu$ with $p\ge2$ and $0<\nu\le1$, and let $\theta,\gamma,c_B,\beta_q$ be the constants of (4.6) and Lemma 4.3. There is a constant $C_B>0$ depending only on $p,\nu$ such that $\theta\le\frac1{16}$, $0<\gamma<\frac\theta2$, and the following holds. Let $L\ge1$, $\mu,R_0>0$, $0<\eta\le\gamma/(2(1+\theta))$, and let $h_0,\dots,h_{L-1}\in\mathbb R^d$ be mutually orthogonal with $\|h_j\|=R_0\eta^j$. Put $c_j=\sum_{k<j}h_k$, $R_j=\|h_j\|$, and let $B_0,\dots,B_L$ be the partial bases of (4.4), $B=B_L$. Then:
--
--   1. **(a)** each $B_j$ ($0\le j\le L$) is convex and $p$ times continuously differentiable with $\|\nabla^pB_j(y)-\nabla^pB_j(x)\|\le C_B\mu\|y-x\|^\nu$, and
--   $$
--   D_B(y,x)\ \ge\ c_B\,\mu\,\|y-x\|^q\qquad\text{for all }x,y;
--   $$
--   2. **(b)** $B(0)=0$, $\nabla B(0)=0$, and for $0\le j<L$
--   $$
--   \nabla B(c_{j+1})-\nabla B(c_j)=\mu R_j^{q-2}h_j,\qquad B(c_{j+1})-B(c_j)=\beta_q\mu R_j^q;
--   $$
--   3. **(c)** for $0\le j<L$, $B_{j+1}=N^B_j$ on $\{\|x-c_{j+1}\|\le\gamma R_j\}$ and $B_{j+1}=B_j$ on $\{\|x-c_{j+1}\|\ge\theta R_j/2\}$; the local formula $B_j(x)=B_j(c_j)+\langle\nabla B_j(c_j),x-c_j\rangle+\frac\mu q\|x-c_j\|^q$ (4.2) holds for all $x$ when $j=0$, and on $\{\|x-c_j\|\le\gamma R_{j-1}\}$ for $1\le j\le L$;
--   4. **(d)** for $0\le j<L$ and every $x$ outside the closed ball $\{\|x-c_{j+1}\|\le\theta R_j\}$, $B(x)=B_j(x)$ and $\nabla^kB(x)=\nabla^kB_j(x)$ for $1\le k\le p$; $B=B_j$ on a neighborhood of $c_j$ for $0\le j\le L$; and $B_j$ depends only on $c_0,\dots,c_j$.
--
--   Here $D_B(y,x)=B(y)-B(x)-\langle\nabla B(x),y-x\rangle$ is the Bregman divergence. The base supplies the uniform convexity and smoothness of the hard instance with constants independent of the number of phases $L$, and the same local geometry at every center.
--
--   **Formalization Note** $D_B$ is the published Bregman divergence `AdaGradDHS.Diag.bregman`. "Depends only on $c_0,\dots,c_j$" is stated as: replacing $h$ by any sequence that agrees with it below $j$ leaves $B_j$ unchanged.
--
--   Differences from the source:
--   - encoding: ℝ^d, ∇^kF, ⟨∇F(x), v⟩ → EuclideanSpace ℝ (Fin d), iteratedFDeriv ℝ k F, fderiv ℝ F x v; reason: Lean convention; the norm of iteratedFDeriv is the operator norm of Sec. 3; same instances
--   - encoding: q = p + ν → a real binder q with the hypothesis hq : q = p + ν; reason: notation only; every instance has q = p + ν
--   - encoding: B_j depends only on the previously chosen centers c_0, …, c_j → any displacement sequence h' with h' i = h i for i < j gives the same baseSeq q μ h' j; reason: c_0, …, c_j are exactly the partial sums of h_0, …, h_{j−1}
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Lemma 4.3, pp.6–7, Eqs. (4.2), (4.4), (4.7)

import Mathlib
import Definitions.Def_MatchedUCLB_baseNB
import Definitions.Def_MatchedUCLB_HolderBound
import Definitions.Def_MatchedUCLB_gam__b2be8d
import Definitions.Def_MatchedUCLB_cB
import Definitions.Def_MatchedUCLB_betaQ
import Definitions.Def_AdaGradDHS_Diag_bregman

open scoped ContDiff Topology

namespace MatchedUCLB

/-- **Lemma 4.3 (uniformly convex base).** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, Lemma 4.3, pp.6–7: "For the constants chosen in
Step 1.3, there is `C_B > 0`, depending only on `p, ν`, such that the following holds. We have
`θ ≤ 1/16` and `0 < γ < θ/2`. For any `L ≥ 1`, `μ, R_0 > 0`, `0 < η ≤ γ/(2(1+θ))`, and mutually
orthogonal `h_0, …, h_{L−1}` with `‖h_j‖ = R_0η^j`, Eq. (4.4) produces convex `B_j ∈ C^{p,ν}(ℝ^d)`
and `B = B_L` satisfying: (a) … for `c_B = 1/(2q·16^{q−2})`, all `x, y`, and `0 ≤ j ≤ L`,
`‖∇^pB_j(y) − ∇^pB_j(x)‖ ≤ C_Bμ‖y − x‖^ν`, `D_B(y, x) ≥ c_Bμ‖y − x‖^q`; (b) `B(0) = 0`,
`∇B(0) = 0`, and, for `0 ≤ j < L`, `∇B(c_{j+1}) − ∇B(c_j) = μR_j^{q−2}h_j`,
`B(c_{j+1}) − B(c_j) = β_qμR_j^q` (4.7); (c) for `0 ≤ j < L`, `B_{j+1}(x) = N^B_j(x)` if
`‖x − c_{j+1}‖ ≤ γR_j` and `= B_j(x)` if `‖x − c_{j+1}‖ ≥ θR_j/2`. Eq. (4.2) holds globally for
`j = 0` and on `‖x − c_j‖ ≤ γR_{j−1}` for `1 ≤ j ≤ L`; (d) for the replacement ball `S_j` and
`0 ≤ j < L`, `B(x) = B_j(x)` and `∇^kB(x) = ∇^kB_j(x)` for `x ∉ S̄_j` and `1 ≤ k ≤ p`. Also, `B = B_j`
on a neighborhood of `c_j` for `0 ≤ j ≤ L`. The partial base `B_j` depends only on the previously
chosen centers `c_0, …, c_j`."

**Formalization Note.** `q` is a separate real binder with the hypothesis `q = p + ν` (the matched order of the paper), so that every formula can be written in `q`. `R_j = ‖h_j‖`, `c_j = center h j`, `B_j = baseSeq q μ h j`. `C_B` is
chosen before the dimension `d` and all data. (4.2) is
`B_j(x) = B_j(c_j) + ⟨∇B_j(c_j), x − c_j⟩ + (μ/q)‖x − c_j‖^q`, with the pairing as `fderiv`. `D_B` is
the published Bregman divergence `AdaGradDHS.Diag.bregman` (`bregman F y x = F y − F x −
⟨∇F(x), y − x⟩`). `S̄_j` is the closed ball `‖x − c_{j+1}‖ ≤ θR_j`, so `x ∉ S̄_j` is
`θR_j < ‖x − c_{j+1}‖`. "Depends only on `c_0, …, c_j`" is stated as: any displacement sequence
agreeing with `h` below `j` (hence with the same `c_0, …, c_j`) gives the same `B_j`. -/
theorem lemma_4_3 (p : ℕ) (hp : 2 ≤ p) (ν : ℝ) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (q : ℝ) (hq : q = (p : ℝ) + ν) :
    ∃ CB : ℝ, 0 < CB ∧ theta q ≤ 1 / 16 ∧ 0 < gam q ∧ gam q < theta q / 2 ∧
    ∀ (d L : ℕ) (μ R₀ η : ℝ) (h : ℕ → EuclideanSpace ℝ (Fin d)),
      1 ≤ L → 0 < μ → 0 < R₀ → 0 < η → η ≤ gam q / (2 * (1 + theta q)) →
      (∀ i j : ℕ, i < L → j < L → i ≠ j → inner ℝ (h i) (h j) = 0) →
      (∀ j : ℕ, j < L → ‖h j‖ = R₀ * η ^ j) →
      -- (a)
      (∀ j : ℕ, j ≤ L → ConvexOn ℝ Set.univ (baseSeq q μ h j) ∧ ContDiff ℝ p (baseSeq q μ h j) ∧
          HolderBound p ν (CB * μ) (baseSeq q μ h j)) ∧
      (∀ x y : EuclideanSpace ℝ (Fin d), cB q * μ * ‖y - x‖ ^ q ≤ AdaGradDHS.Diag.bregman (baseSeq q μ h L) y x) ∧
      -- (b)
      baseSeq q μ h L 0 = 0 ∧ gradient (baseSeq q μ h L) 0 = 0 ∧
      (∀ j : ℕ, j < L →
        gradient (baseSeq q μ h L) (center h (j + 1)) - gradient (baseSeq q μ h L) (center h j) =
            (μ * ‖h j‖ ^ (q - 2)) • h j ∧
        baseSeq q μ h L (center h (j + 1)) - baseSeq q μ h L (center h j) = betaQ q * μ * ‖h j‖ ^ q) ∧
      -- (c)
      (∀ j : ℕ, j < L → ∀ x : EuclideanSpace ℝ (Fin d), ‖x - center h (j + 1)‖ ≤ gam q * ‖h j‖ →
        baseSeq q μ h (j + 1) x = baseNB q μ h j x) ∧
      (∀ j : ℕ, j < L → ∀ x : EuclideanSpace ℝ (Fin d), theta q * ‖h j‖ / 2 ≤ ‖x - center h (j + 1)‖ →
        baseSeq q μ h (j + 1) x = baseSeq q μ h j x) ∧
      (∀ x : EuclideanSpace ℝ (Fin d), baseSeq q μ h 0 x = baseSeq q μ h 0 (center h 0) +
        fderiv ℝ (baseSeq q μ h 0) (center h 0) (x - center h 0) + μ / q * ‖x - center h 0‖ ^ q) ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ L → ∀ x : EuclideanSpace ℝ (Fin d), ‖x - center h j‖ ≤ gam q * ‖h (j - 1)‖ →
        baseSeq q μ h j x = baseSeq q μ h j (center h j) +
          fderiv ℝ (baseSeq q μ h j) (center h j) (x - center h j) + μ / q * ‖x - center h j‖ ^ q) ∧
      -- (d)
      (∀ j : ℕ, j < L → ∀ x : EuclideanSpace ℝ (Fin d), theta q * ‖h j‖ < ‖x - center h (j + 1)‖ →
        baseSeq q μ h L x = baseSeq q μ h j x ∧
        ∀ k : ℕ, 1 ≤ k → k ≤ p → iteratedFDeriv ℝ k (baseSeq q μ h L) x = iteratedFDeriv ℝ k (baseSeq q μ h j) x) ∧
      (∀ j : ℕ, j ≤ L → baseSeq q μ h L =ᶠ[𝓝 (center h j)] baseSeq q μ h j) ∧
      (∀ j : ℕ, j ≤ L → ∀ h' : ℕ → EuclideanSpace ℝ (Fin d), (∀ i : ℕ, i < j → h' i = h i) →
        baseSeq q μ h' j = baseSeq q μ h j) := by sorry

end MatchedUCLB
