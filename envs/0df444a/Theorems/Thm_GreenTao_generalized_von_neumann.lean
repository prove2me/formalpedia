-- Prove2me | Theorems.Thm_GreenTao_generalized_von_neumann
-- name    : GreenTao.generalized_von_neumann
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T20:54:02.346689+00:00
-- url     : https://prove2.me/theorems/0dc70093-6baa-485e-b594-70796304398f
-- title:
--   Generalized von Neumann estimate with uniform cube thresholds
-- statement:
--   Let $k\ge3$, let $M_n$ be prime moduli tending to infinity, and let $\nu_n$ be a $k$-pseudorandom family. For every $\eta>0$ there is $\rho>0$ such that, for all sufficiently large $n$, the following holds uniformly over all tuples of real functions $F_0,\ldots,F_{k-1}$ on $G_n=\mathbb Z/M_n\mathbb Z$:
--
--   $$\left(\forall j,x,\ |F_j(x)|\le\nu_n(x)+2\right)\ \text{and}\ \left(\exists j,\ |C_{k-1}(F_j)|\le\rho\right)$$
--
--   imply
--
--   $$\left|\mathbb E_{x,r\in G_n}\prod_{j=0}^{k-1}F_j(x+jr)\right|\le\eta.$$
--
--   Here $C_d$ is the real Gowers cube average. One sufficiently uniform factor makes a mixed progression average small. The threshold is chosen before the modulus and the tuple of functions; this uniformity is needed to apply the estimate to functions supplied by a structured decomposition.
--
--   **Formalization Note.** This is the qualitative threshold form of Proposition 5.3 for consecutive coefficients $c_j=j$. Its additive constant is $2$ in place of $1$, obtained by the fixed convex-mixture/rescaling allowed by Lemma 3.4. Smallness is stated in terms of the $2^{k-1}$-th power of the Gowers norm.
-- source:
--   Green and Tao, The primes contain arbitrarily long arithmetic progressions, https://arxiv.org/html/math/0404188v6, §5 Proposition 5.3 and its proof, together with §3 Lemma 3.4 (including the stated extension to (1−θ)ν+θν_const) for the harmless change from ν+1 to ν+2; §5 equations (5.1), (5.4) for the cube power. The epsilon/rho statement is an equivalent qualitative uniform consequence of its O(inf_j ||F_j||_U)+o(1) estimate.

import Definitions.Def_GreenTao_Uniformity
open Filter

theorem GreenTao.generalized_von_neumann
    (k : ℕ) (hk : 3 ≤ k) (M : ℕ → ℕ+)
    (hprime : ∀ n, Nat.Prime (M n : ℕ))
    (hM : Tendsto (fun n => (M n : ℕ)) atTop atTop)
    (ν : GreenTao.Family M) (hν : GreenTao.Pseudorandom k M ν)
    (η : ℝ) (hη : 0 < η) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ᶠ n in atTop,
      ∀ F : Fin k → ZMod (M n : ℕ) → ℝ,
        (∀ j x, |F j x| ≤ ν n x + 2) →
        (∃ j, |GreenTao.cubeAvg (k - 1) (F j)| ≤ ρ) →
        |GreenTao.mixedAPAvg k F| ≤ η := by sorry
