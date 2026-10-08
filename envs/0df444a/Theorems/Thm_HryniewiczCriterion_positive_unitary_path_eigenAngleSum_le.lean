-- Prove2me | Theorems.Thm_HryniewiczCriterion_positive_unitary_path_eigenAngleSum_le
-- name    : HryniewiczCriterion.positive_unitary_path_eigenAngleSum_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-06T20:36:34.407515+00:00
-- url     : https://prove2.me/theorems/e641043c-dde4-4afa-8c1d-1ab170f3e753
-- title:
--   A positive unitary path from the identity winds at least as far as its endpoint eigen-angles
-- statement:
--   Let $V:[0,T]\to U(n)$, $T>0$, be a differentiable path of unitary matrices with $V(0)=I$ and
--   $$V'(t)=i\,Q(t)\,V(t),\qquad Q(t)\ \text{Hermitian positive definite}.$$
--   Let $\theta$ be a continuous determinant angle, $\det V(t)=e^{i\theta(t)}$ with $\theta(0)=0$. Then
--   $$\theta(T)\ \ge\ \sum_{\lambda}\operatorname{ang}(\lambda),$$
--   where the sum runs over the eigenvalues $\lambda$ of $V(T)$ with algebraic multiplicity, and $\operatorname{ang}(\lambda)\in(0,2\pi]$ is the argument normalized so that $\operatorname{ang}(1)=2\pi$.
--
--   Proof idea: the eigenvalues of a positive unitary path move strictly counterclockwise. Near any $t_0$, choose $a$ on the unit circle that is not an eigenvalue of $V(t_0)$; the Cayley transform $C(t)=i(a+V(t))(a-V(t))^{-1}$ is Hermitian with $C'(t)>0$. Counting eigenvalues of $C(t)$ above a level (min–max) shows that $E(t)=\theta(t)-\sum\operatorname{ang}$ is locally nondecreasing, hence nondecreasing on $(0,T]$. At $t=0^+$ all $n$ eigenvalues leave $1$ counterclockwise, so $E(0^+)=0$.
-- source:
--   Monotonicity of eigenvalues of positive unitary paths (Krein theory; cf. Robbin–Salamon, The Maslov index for paths, Topology 32 (1993), https://doi.org/10.1016/0040-9383(93)90052-W, and Ekeland, Convexity Methods in Hamiltonian Mechanics, Springer 1990, Ch. I). Finite-dimensional replacement for the spectral-flow count in Hofer–Wysocki–Zehnder, The dynamics on three-dimensional strictly convex energy surfaces, Ann. of Math. 148 (1998), https://doi.org/10.2307/120994, proof of Theorem 3.4, (3.42)–(3.43), pp. 221–222.

import Definitions.Def_HryniewiczCriterion_GraphAngle

open HryniewiczCriterion
open scoped ContDiff ComplexOrder

theorem HryniewiczCriterion.positive_unitary_path_eigenAngleSum_le {n : Type} [Fintype n] [DecidableEq n]
    (V Q : ℝ → Matrix n n ℂ) (T : ℝ) (hT : 0 < T) (h0 : V 0 = 1)
    (hU : ∀ t ∈ Set.Icc 0 T, star (V t) * V t = 1)
    (hQ : ∀ t ∈ Set.Icc 0 T, (Q t).PosDef)
    (hd : ∀ t ∈ Set.Icc 0 T, ∀ i j : n,
      HasDerivAt (fun s => V s i j) ((Complex.I • (Q t * V t)) i j) t)
    (θ : ℝ → ℝ) (hθ : IsDetAngleLift V T θ) :
    eigenAngleSum (V T) ≤ θ T := by sorry
