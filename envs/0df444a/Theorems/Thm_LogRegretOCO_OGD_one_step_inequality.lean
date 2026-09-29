-- Prove2me | Theorems.Thm_LogRegretOCO_OGD_one_step_inequality
-- name    : LogRegretOCO.OGD.one_step_inequality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T21:33:06.660983+00:00
-- url     : https://prove2.me/theorems/a642e1b7-c872-4f19-bfcf-6b87da74b927
-- title:
--   Eq. (2) — one projected gradient step: 2∇ᵀ(x − u) ≤ (‖x − u‖² − ‖x' − u‖²)/η + ηG²
-- statement:
--   Let $\mathcal P\subseteq\mathbb R^n$ be convex, let $x,g\in\mathbb R^n$, let $\eta>0$ and $G\in\mathbb R$ with $\|g\|_2\le G$, and let $z=\Pi_{\mathcal P}(x-\eta g)$ be the Euclidean projection of the gradient step $x-\eta g$ onto $\mathcal P$. Then for every $u\in\mathcal P$,
--   $$\|z-u\|_2^2\ \le\ \|x-u\|_2^2+\eta^2\|g\|_2^2-2\eta\, g^\top(x-u),$$
--   $$2\,g^\top(x-u)\ \le\ \frac{\|x-u\|_2^2-\|z-u\|_2^2}{\eta}+\eta\,G^2 .$$
--
--   This is display (2) in the proof of Theorem 1, applied there with $x=x_t$, $g=\nabla f_t(x_t)$, $\eta=\eta_{t+1}$, $z=x_{t+1}$ and $u=x^*$. It bounds the linearised regret of one round by a telescoping difference of squared distances plus a step-size term, which is Zinkevich's analysis of projected gradient descent.
--
--   **Formalization Note** The paper prints the second line as "$5\nabla_t^\top(x_t-x^*)\le\dots$"; the $5$ is a typo for $2$: the line follows from the first one by rearranging, and the proof then sums (2) against (1), which needs the factor $2$. The Lean states $2$. The point $x$ is not required to lie in $\mathcal P$ (the inequality holds anyway), and the comparator is any $u\in\mathcal P$ rather than the minimiser $x^*$. Points are `EuclideanSpace ℝ (Fin n)`.
-- source:
--   Hazan, Agarwal, Kale, Logarithmic regret algorithms for online convex optimization, Mach Learn 69 (2007), p. 175, proof of Theorem 1, Eq. (2)

import Mathlib
import Definitions.Def_LogRegretOCO_OGD_Model

namespace LogRegretOCO.OGD

/-- **Eq. (2)** (p. 175): one projected gradient step `z = Π_P(x − η g)` with `η > 0`,
`‖g‖ ≤ G`, measured against any `u ∈ P`:
`‖z − u‖² ≤ ‖x − u‖² + η² ‖g‖² − 2η gᵀ(x − u)` and
`2 gᵀ(x − u) ≤ (‖x − u‖² − ‖z − u‖²)/η + η G²`.
(The paper prints `5∇_t^⊤` in the second line; it is `2∇_t^⊤`.) -/
theorem one_step_inequality {n : ℕ} (P : Set (E n)) (hPc : Convex ℝ P) (x g z u : E n)
    (η G : ℝ) (hη : 0 < η) (hg : ‖g‖ ≤ G) (hz : IsProj P (x - η • g) z) (hu : u ∈ P) :
    ‖z - u‖ ^ 2 ≤ ‖x - u‖ ^ 2 + η ^ 2 * ‖g‖ ^ 2 - 2 * η * inner ℝ g (x - u) ∧
      2 * inner ℝ g (x - u) ≤ (‖x - u‖ ^ 2 - ‖z - u‖ ^ 2) / η + η * G ^ 2 := by sorry

end LogRegretOCO.OGD
