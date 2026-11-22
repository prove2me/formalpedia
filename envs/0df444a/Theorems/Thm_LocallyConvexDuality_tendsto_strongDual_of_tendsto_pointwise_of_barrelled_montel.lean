-- Prove2me | Theorems.Thm_LocallyConvexDuality_tendsto_strongDual_of_tendsto_pointwise_of_barrelled_montel
-- name    : LocallyConvexDuality.tendsto_strongDual_of_tendsto_pointwise_of_barrelled_montel
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:31:41.281812+00:00
-- url     : https://prove2.me/theorems/cb7af88d-507b-46c0-98c1-ce1bbca25c0f
-- title:
--   Remark B.4.1.6 — on a barrelled Montel space, a pointwise convergent sequence of continuous functionals converges in the strong dual
-- statement:
--   **Weak-$*$ convergent sequences in the dual of a barrelled Montel space converge strongly** (Remark B.4.1.6).
--
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$ and let $E$ be a Hausdorff locally convex space over $\mathbb K$ which is
--
--   - *barrelled*, and
--   - such that every closed bounded subset of $E$ is compact (the Heine–Borel property; together with barrelledness this says that $E$ is a Montel space).
--
--   Let $(\varphi_n)_{n\in\mathbb N}$ be a sequence of continuous linear functionals on $E$ which converges pointwise: there is a function $f\colon E\to\mathbb K$ with $\varphi_n(x)\to f(x)$ for every $x\in E$. Then:
--
--   1. $f$ is a continuous linear functional: there is $F\in E'$ with $F(x)=f(x)$ for all $x\in E$;
--   2. $\varphi_n\to F$ uniformly on every bounded subset $B$ of $E$:
--   $$\sup_{x\in B}|\varphi_n(x)-F(x)|\longrightarrow0\qquad(n\to\infty);$$
--   3. equivalently, $\varphi_n\to F$ in the strong dual $E'_\beta$.
--
--   This is the classical reason why, for sequences of distributions or of tempered distributions, weak convergence is the same as strong convergence. The source records the argument in Remark B.4.1.6 for $E=\mathcal S(\mathbb R)$, to see that the local Dirac comb $D_{\chi,\mathfrak p}=\sum_{m>0}\chi(\mathfrak p^m)N(\mathfrak p)^{m\sigma}\delta_{N(\mathfrak p)^m}$ converges in $\mathcal S(\mathbb R)'_\beta$, and uses it again for $E=\mathcal D(C_F)$ at the end of the proof of Theorem B.4.4.7.
--
--   **Formalization Note.** "Locally convex" is Mathlib's `PolynormableSpace 𝕜 E` (the topology is defined by a family of seminorms; for `RCLike 𝕜` this is equivalent to local convexity), "barrelled" is `BarrelledSpace 𝕜 E`, and the Heine–Borel property is Mathlib's class `MontelSpace 𝕜 E` (which by design does not include barrelledness). Bounded sets are the von Neumann bounded sets, `Bornology.IsVonNBounded 𝕜`. `StrongDual 𝕜 E` is `E →L[𝕜] 𝕜` with Mathlib's topology of uniform convergence on bounded sets, so the last conjunct `Tendsto φ atTop (𝓝 F)` is convergence in $E'_\beta$; the middle conjunct spells the same convergence out with `TendstoUniformlyOn`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 611, Remark B.4.1.6 (used again on pp. 625-626, end of the proof of Theorem B.4.4.7); classical reference: H. H. Schaefer, with M. P. Wolff, Topological Vector Spaces, Second Edition, Springer, Ch. IV, 4.6 (so printed in the paper) and Ch. I, 5.1 (as cited by the paper)

import Mathlib

open Filter Topology

set_option autoImplicit false

namespace LocallyConvexDuality

theorem tendsto_strongDual_of_tendsto_pointwise_of_barrelled_montel
    {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [PolynormableSpace 𝕜 E] [T2Space E]
    [BarrelledSpace 𝕜 E] [MontelSpace 𝕜 E]
    (φ : ℕ → StrongDual 𝕜 E) (f : E → 𝕜)
    (hφ : ∀ x : E, Tendsto (fun n : ℕ => φ n x) atTop (𝓝 (f x))) :
    ∃ F : StrongDual 𝕜 E, (∀ x : E, F x = f x) ∧
      (∀ B : Set E, Bornology.IsVonNBounded 𝕜 B →
        TendstoUniformlyOn (fun (n : ℕ) (x : E) => φ n x) (fun x : E => F x) atTop B) ∧
      Tendsto φ atTop (𝓝 F) := by sorry

end LocallyConvexDuality
