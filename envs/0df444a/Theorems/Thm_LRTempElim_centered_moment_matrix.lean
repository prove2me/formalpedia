-- Prove2me | Theorems.Thm_LRTempElim_centered_moment_matrix
-- name    : LRTempElim.centered_moment_matrix
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T03:27:21.181186+00:00
-- url     : https://prove2.me/theorems/339de1d4-f4fb-4f20-a861-fc74fa3903a0
-- title:
--   §A.2.3: the centered moment matrix depends on $c_t$ only and is uniformly invertible
-- statement:
--   Write $X_0=U-a/2$, $X_1=V+a/2$ with $U,V$ independent standard Gaussians, so that $X_t=\mu_t+Z_t$ with $\mu_t=(t-\tfrac12)a$, $Z_t=(1-t)U+tV$ and $c_t=\mathrm{Var}\,Z_t=(1-t)^2+t^2$. Let
--   $$
--   \widetilde M(c)=\begin{pmatrix}1&0&c\\0&c&0\\c&0&3c^2\end{pmatrix},\qquad L_{a,t}=\begin{pmatrix}1&0&0\\\mu_t&1&0\\\mu_t^2&2\mu_t&1\end{pmatrix}.
--   $$
--   For every $a$ and every $t\in[0,1]$:
--
--   1. in the centered basis $(1,Z_t,Z_t^2)$ the population moment matrix is $\mathbb E[(1,Z_t,Z_t^2)^\top(1,Z_t,Z_t^2)]=\widetilde M(c_t)$, which depends on $c_t$ but not on $a$;
--   2. the moment matrix in the original basis is $M_t=L_{a,t}\widetilde M(c_t)L_{a,t}^\top$, because $\phi(\mu_t+z)=L_{a,t}(1,z,z^2)^\top$;
--   3. $c_t\in[1/2,1]$;
--   4. $\widetilde M(c_t)$ is invertible;
--   5. there is one constant $K$ such that every entry of $\widetilde M(c_t)$ and of $\widetilde M(c_t)^{-1}$ is at most $K$ in absolute value for all $t\in[0,1]$.
--
--   These facts give the uniform control in $t$ that underlies the polynomial upper bound on $C_{\mathrm{path}}(a)$.
--
--   Differences from the source:
--   - reading: "in the centered basis (1, Z_t, Z_t²), the population moment matrix … depend[s] on c_t but not a" → its closed form M̃(c_t) = [[1,0,c_t],[0,c_t,0],[c_t,0,3c_t²]], together with the change of basis M_t = L M̃(c_t) L⊤; reason: the closed form displays the dependence on c_t alone; the change of basis ties it to the moment matrix of (51)
--   - reading: "its inverse … [is] uniformly bounded in t" → M̃(c_t) is invertible and one constant K bounds the entries of M̃(c_t) and M̃(c_t)⁻¹ for all t ∈ [0,1]; reason: entrywise uniform bound; K is free of a, as the sentence says
-- source:
--   Chen, Wu, Yang, Zeng, Likelihood-Ratio Learning under Weak Overlap via Analytic Temporal Elimination, STOC 2027 submission (manuscript of 2026-11-03, sha256 eee651394d60e9274fc77c5a1bd08841eb53ee6030924de85b47f5a195371758), §A.2.3, p.20 (pdf p.22)

import Mathlib
import Definitions.Def_LRTempElim_PathEstimator

open MeasureTheory ProbabilityTheory Matrix

namespace LRTempElim

/-- **Centered moment matrix** (§A.2.3). Chen, Wu, Yang, Zeng, *Likelihood-Ratio Learning under
Weak Overlap via Analytic Temporal Elimination*, STOC 2027 submission (manuscript of 2026-11-03,
sha256 eee65139…), §A.2.3, p.20 (pdf p.22).

"For the polynomial path-estimator upper order, write `X₀ = U − a/2` and `X₁ = V + a/2`, so
`X_t = µ_t + Z_t` with `µ_t = (t − 1/2)a` and `Z_t = (1 − t)U + tV`, where U, V are independent
standard Gaussians and `c_t = Var Z_t = (1−t)² + t² ∈ [1/2, 1]`. In the centered basis
`(1, Z_t, Z_t²)`, the population moment matrix and its inverse depend on `c_t` but not a, and are
uniformly bounded in t."

**Formalization Note.** `Z_t = X_t − µ_t` under `W = (X₀, X₁) ∼ Q_a ⊗ P_a` (`pairLaw a`), so the
centered basis is `phi3 (X_t − µ_t) = (1, Z_t, Z_t²)`. Its moment matrix is stated in closed form,
`M̃(c) = [[1, 0, c], [0, c, 0], [c, 0, 3c²]]` at `c = c_t` (the Gaussian moments of `Z_t ∼ N(0, c_t)`),
which displays "depends on `c_t` but not `a`". "The population moment matrix in the centered basis"
is tied to `M_t = momentMat phi3 a t` by `ϕ(µ + z) = Lϕ(z)`, `L = [[1,0,0],[µ,1,0],[µ²,2µ,1]]`, i.e.
`M_t = L M̃(c_t) L⊤`. "Its inverse" is asserted to exist (`det ≠ 0`), and "uniformly bounded in t"
is one constant `K` bounding all entries of `M̃(c_t)` and `M̃(c_t)⁻¹` for `t ∈ [0, 1]` (it is free
of `a`). Time ranges over `[0, 1]`. -/
theorem centered_moment_matrix :
    let Mc : ℝ → Matrix (Fin 3) (Fin 3) ℝ := fun c => !![1, 0, c; 0, c, 0; c, 0, 3 * c ^ 2]
    let L : ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ := fun a t =>
      !![1, 0, 0; bridgeMean a t, 1, 0; bridgeMean a t ^ 2, 2 * bridgeMean a t, 1]
    (∀ a : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Matrix.of (fun i j => ∫ W, phi3 (bridge t W - bridgeMean a t) i *
          phi3 (bridge t W - bridgeMean a t) j ∂(pairLaw a)) = Mc (bridgeVar t)) ∧
    (∀ a : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      momentMat phi3 a t = L a t * Mc (bridgeVar t) * (L a t)ᵀ) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, bridgeVar t ∈ Set.Icc (1 / 2 : ℝ) 1) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, (Mc (bridgeVar t)).det ≠ 0) ∧
    (∃ K : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i j : Fin 3,
      |Mc (bridgeVar t) i j| ≤ K ∧ |(Mc (bridgeVar t))⁻¹ i j| ≤ K) := by sorry

end LRTempElim
