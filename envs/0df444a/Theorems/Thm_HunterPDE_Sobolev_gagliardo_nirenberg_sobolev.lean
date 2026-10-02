-- Prove2me | Theorems.Thm_HunterPDE_Sobolev_gagliardo_nirenberg_sobolev
-- name    : HunterPDE.Sobolev.gagliardo_nirenberg_sobolev
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T06:57:54.832607+00:00
-- url     : https://prove2.me/theorems/05bda57e-bddd-4545-85a9-86539e325223
-- title:
--   Theorem 3.28 — Gagliardo–Nirenberg–Sobolev inequality with an explicit constant
-- statement:
--   Let $n \ge 2$, $1 \le p < n$, and let $p^* = np/(n-p)$ be the Sobolev conjugate of $p$ (Definition 3.25). Then for every $f \in C_c^\infty(\mathbb{R}^n)$
--   $$\|f\|_{p^*} \le \frac{p\,(n-1)}{2\,(n-p)}\, \|Df\|_p ,$$
--   where $\|Df\|_p = \big(\int_{\mathbb{R}^n} |Df|^p\, dx\big)^{1/p}$ and $|Df| = \big(\sum_i (\partial_i f)^2\big)^{1/2}$ is the Euclidean length of the gradient.
--
--   The inequality says that a compactly supported smooth function whose gradient is in $L^p$ is itself in $L^{p^*}$, with $p^* > p$: one derivative in $L^p$ buys integrability $p^*$. It underlies every Sobolev embedding for $p < n$, e.g. $W^{1,p}(\mathbb{R}^n) \hookrightarrow L^q(\mathbb{R}^n)$ for $p \le q \le p^*$ (Theorem 3.31).
--
--   **Formalization Note.** The constant is $n$ times the constant $C(n,p) = \frac{p}{2n}\cdot\frac{n-1}{n-p}$ printed in (3.11). With the Euclidean $|Df|$ the printed constant is false: at $p = 1$ it is $\frac1{2n}$, below the sharp constant $\frac{1}{n\alpha_n^{1/n}}$ the notes themselves quote on p. 65–66 ($\alpha_n$ the volume of the unit ball), and it is also below Talenti's sharp constant for some $1 < p < n$ (e.g. $n = 4$, $p = 1.2$). The error is in the last step of the proof, which replaces $(\prod_i \|\partial_i f\|_p)^{1/n}$ by $\frac1n (\sum_i \|\partial_i f\|_p^p)^{1/p}$. The proof's display $\|f\|_{p^*} \le \frac{s}{2} (\prod_{i} \|\partial_i f\|_p)^{1/n}$ with $s = \frac{p(n-1)}{n-p}$, which is correct, together with $|\partial_i f| \le |Df|$, gives the constant $\frac s2$ stated here. $\mathbb{R}^n$ is `EuclideanSpace ℝ (Fin n)`; $|Df|$ is `‖gradient f x‖`, which equals the operator norm of `fderiv ℝ f x`; norms are `eLpNorm` in $[0,\infty]$ with exponents `ENNReal.ofReal p` and `ENNReal.ofReal p*`; $C_c^\infty$ is `ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ HasCompactSupport f`.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 63, Theorem 3.28 (constant corrected; see the Formalization Note)

import Mathlib
import Definitions.Def_HunterPDE_Sobolev_SobolevConjugate

open MeasureTheory

namespace HunterPDE.Sobolev

/-- Theorem 3.28 of Hunter, *Notes on PDEs* (revised 6/18/2014), p. 63 (Gagliardo–Nirenberg–Sobolev
inequality), with the constant its proof establishes. Let `n ≥ 2`, `1 ≤ p < n` and
`p* = np/(n − p)` (Definition 3.25). Then for every `f ∈ C_c^∞(ℝⁿ)`
`‖f‖_{p*} ≤ C ‖Df‖_p` with `C = p(n − 1) / (2(n − p))`, where `|Df|` is the Euclidean norm of the
gradient. The printed constant (3.11), `p(n − 1)/(2n(n − p))`, is `1/n` times this and is false
with the Euclidean `|Df|` (it is below the book's own sharp constant `1/(n αₙ^{1/n})` at `p = 1`);
the proof's display `‖f‖_{p*} ≤ (s/2) (∏ᵢ ‖∂ᵢf‖_p)^{1/n}`, `s = p(n−1)/(n−p)`, together with
`|∂ᵢf| ≤ |Df|`, gives the constant stated here. -/
theorem gagliardo_nirenberg_sobolev {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : 1 ≤ p) (hpn : p < n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hfc : HasCompactSupport f) :
    eLpNorm f (ENNReal.ofReal (sobolevConjugate n p)) volume ≤
      ENNReal.ofReal (p * ((n : ℝ) - 1) / (2 * ((n : ℝ) - p))) *
        eLpNorm (fun x => ‖gradient f x‖) (ENNReal.ofReal p) volume := by sorry

end HunterPDE.Sobolev
