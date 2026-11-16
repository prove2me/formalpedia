-- Prove2me | Theorems.Thm_KhintchineTwoRegime_Supplement_theorem_4
-- name    : KhintchineTwoRegime.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:26:46.63799+00:00
-- url     : https://prove2.me/theorems/7a442730-52ed-46e9-8313-04556d09878e
-- title:
--   Theorem 4 — every Boolean LTF has $W^{\le1}\ge(7423/10000)^2=0.55100929$
-- statement:
--   For a function $h$ on the Hamming cube $\{-1,1\}^n$ (uniform measure) let $W^{\le1}(h)=\sum_{|S|\le1}\hat h(S)^2$ be its low-degree Fourier weight, including $\hat h(\emptyset)^2$. A Boolean linear threshold function is $f(x)=\operatorname{sgn}(\omega_0+\omega_1x_1+\dots+\omega_nx_n)$ with real $\omega_0,\dots,\omega_n$ and $\operatorname{sgn}(0)=1$.
--
--   **Theorem 4 (Explicit low-degree Fourier weight of LTFs).** Let $W^{\le1}[\mathrm{LTF}]=\inf\{W^{\le1}[f]: f\text{ a Boolean linear threshold function on a finite cube}\}$. Then
--   $$
--   W^{\le1}[\mathrm{LTF}]\ge\Bigl(\frac{7423}{10000}\Bigr)^2=\frac{55100929}{100000000}=0.55100929 .
--   $$
--   Equivalently: every linear threshold function $f$ on every cube $\{-1,1\}^n$ satisfies $W^{\le1}(f)\ge(7423/10000)^2$.
--
--   The classical bound is $W^{\le1}[\mathrm{LTF}]\ge1/2$, De, Diakonikolas and Servedio showed $1/2+\epsilon$ for some unspecified $\epsilon>0$, and the Benjamini–Kalai–Schramm conjecture asks for $2/\pi$; this theorem makes the improvement over $1/2$ explicit.
--
--   **Formalization Note** The cube is encoded as `Fin n → Bool` with true $\mapsto+1$, the encoding of $K_n$, and the uniform expectation is the $2^{-n}$-weighted finite sum. The threshold and the weights are arbitrary reals and ties are allowed.
--
--   Differences from the source:
--
--   - encoding: W≤1[LTF] = inf{W≤1[f] : f an LTF on a finite cube} ≥ (7423/10000)² → ∀ n, ∀ f with IsLTF f, (7423/10000)² ≤ W≤1(f); reason: a lower bound on the infimum of a nonempty set of reals is the same as a lower bound on every member
--   - generalization: cubes {−1,1}ⁿ with n ∈ ℤ⁺ → every n : ℕ, including n = 0; reason: on the 0-dimensional cube every LTF is constant with W≤1 = 1 ≥ (7423/10000)², and restricting to n ≥ 1 gives the source's statement
--   - encoding: f : {−1,1}ⁿ → {−1,1} given by sgn(ω₀ + ∑ ωᵢxᵢ) → f : (Fin n → Bool) → ℝ with IsLTF f (true ↦ +1, false ↦ −1); reason: IsLTF forces the values ±1, and the Bool encoding is the one of the published K
-- source:
--   Fang–Wang, A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), Theorem 4, eq. (22), p.11 (LTF, sgn, Fourier coefficients and W≤1 from §4, p.10)

import Mathlib
import Definitions.Def_KhintchineTwoRegime_Supplement_lowDegWeight
import Definitions.Def_KhintchineTwoRegime_Supplement_IsLTF

namespace KhintchineTwoRegime.Supplement

/-- Theorem 4 (Explicit low-degree Fourier weight of LTFs) (Fang–Wang, *A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions*, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), Theorem 4, eq. (22), p.11):
`W≤1[LTF] = inf{W≤1[f] : f a Boolean LTF on a finite cube} ≥ (7423/10000)² = 0.55100929`.

**Formalization Note** Stated pointwise: every LTF `f` on every cube `{−1,1}ⁿ` has
`W≤1(f) ≥ (7423/10000)²`. This is equivalent to the infimum form (the set of values is
nonempty, as constants are LTFs). `n = 0` is included (the paper takes `n ≥ 1`); there `f`
is constant and `W≤1(f) = 1`. -/
theorem theorem_4 (n : ℕ) (f : (Fin n → Bool) → ℝ) (hf : IsLTF f) :
    ((7423 : ℝ) / 10000) ^ 2 ≤ lowDegWeight f := by sorry

end KhintchineTwoRegime.Supplement
