-- Prove2me | Theorems.Thm_MeanFieldOpt_ControlDuality_lemma_7_3
-- name    : MeanFieldOpt.ControlDuality.lemma_7_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T04:28:36.269978+00:00
-- url     : https://prove2.me/theorems/0facd703-fceb-42df-b421-3f07d745a8ce
-- title:
--   Lemma 7.3 — $V$ solves the HJB equation (4.7) on $[0,1]\times(-1,1)$
-- statement:
--   Let $\xi$ be a mixture that is not identically zero, $\gamma\in\mathsf{SF}_+$, $\nu(t)=\int_t^1\xi''(s)\gamma(s)\,ds$, and $V$ the function of Eq. (7.2). Then $V$ solves the Hamilton–Jacobi–Bellman equation (4.7):
--
--   1. $V(1,z)=0$ for all $z\in(-1,1)$;
--   2. for every $t\in[0,1)$, $V(t,\cdot)$ is twice continuously differentiable on $(-1,1)$, and for every $z\in(-1,1)$: $\nu(t)+\partial_z^2V(t,z)<0$, $V(\cdot,z)$ has a right derivative $\partial_tV(t,z)$ at $t$, and
--   $$\partial_tV(t,z)+\xi''(t)\sup_{\lambda\in\mathbb R}\Big\{\lambda+\frac{\lambda^2}{2}\big(\nu(t)+\partial_z^2V(t,z)\big)\Big\}-\frac12\nu(t)=0 .$$
--
--   This is the analytic half of the verification argument: a classical solution of the HJB equation bounds the value of every admissible control.
--
--   **Formalization Note** The inequality $\nu(t)+\partial_z^2V(t,z)<0$ is proved on the page and is part of the statement; it is what makes the supremum over $\lambda$ finite (equal to $-1/(2(\nu+\partial_z^2V))$), so that the real supremum in Lean is the true one. The time derivative is one-sided from the right because $\gamma$ may jump. The hypothesis that some $c_k\neq0$ is added: for $\xi\equiv0$, $V\equiv0$ on $[0,1]\times(-1,1)$ and $\nu+\partial_z^2V=0$.
-- source:
--   El Alaoui, Montanari, Sellke, Optimization of Mean-field Spin Glasses, arXiv:2001.00904v1, p. 36, Lemma 7.3 (HJB equation (4.7), p. 12)

import Mathlib
import Definitions.Def_MeanFieldOpt_ControlDuality_Parisi

open Set

namespace MeanFieldOpt.ControlDuality

/-- Lemma 7.3 (arXiv:2001.00904v1, p. 36), for a mixture that is not identically zero: the
function `V` of Eq. (7.2) solves the HJB equation (4.7) on `[0, 1] × (−1, 1)`, namely
1. `V(1, z) = 0` for `z ∈ (−1, 1)`;
2. for every `t ∈ [0, 1)`, `V(t, ·)` is `C²` on `(−1, 1)`, and for every `z ∈ (−1, 1)`:
   `ν(t) + ∂_z² V(t, z) < 0`, `V(·, z)` has a right time derivative `∂_t V(t, z)` at `t`, and
   `∂_t V(t, z) + ξ''(t) sup_{λ ∈ ℝ} {λ + (λ²/2)(ν(t) + ∂_z² V(t, z))} − ½ ν(t) = 0`. -/
theorem lemma_7_3 (ξ : Mixture) (hξ : ∃ k, ξ.c k ≠ 0) (d : SFData) :
    (∀ z ∈ Ioo (-1 : ℝ) 1, V ξ d 1 z = 0) ∧
    ∀ t ∈ Ico (0 : ℝ) 1,
      ContDiffOn ℝ 2 (V ξ d t) (Ioo (-1 : ℝ) 1) ∧
      ∀ z ∈ Ioo (-1 : ℝ) 1,
        nu ξ d t + deriv (deriv (V ξ d t)) z < 0 ∧
        ∃ Dt : ℝ, HasDerivWithinAt (fun s => V ξ d s z) Dt (Ici t) t ∧
          Dt + ξ.xi'' t * sSup (range fun l : ℝ =>
              l + l ^ 2 / 2 * (nu ξ d t + deriv (deriv (V ξ d t)) z))
            - (1 / 2) * nu ξ d t = 0 := by sorry

end MeanFieldOpt.ControlDuality
