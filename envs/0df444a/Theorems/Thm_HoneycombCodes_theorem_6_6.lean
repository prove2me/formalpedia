-- Prove2me | Theorems.Thm_HoneycombCodes_theorem_6_6
-- name    : HoneycombCodes.theorem_6_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:30:55.535446+00:00
-- url     : https://prove2.me/theorems/cb3a09ba-1589-4e3d-9b8b-d271f8c403fe
-- title:
--   Theorem 6.6 — the entropy-balanced perturbation
-- statement:
--   For every $0<\delta<1/2$,
--
--   $$
--   \kappa_{HC}(\delta)\le\kappa_{bal}(\delta)<\kappa_H(\delta). \tag{70}
--   $$
--
--   More precisely, let $(a,b)$ be any minimizing whole-cube point from Lemma 6.2, let $P_0=(a-b)(1-a-b)/(a(1-a))$ (64), and put
--
--   $$
--   q:=\frac{a(1-a)(1-P_0)}{1-2b}=\frac{b(1-b)}{1-2b}>0 .
--   $$
--
--   On the exact balanced spectral boundary with $x=a$, $u=at$, $v=(1-a)t$ (that is, $\eta=\sin^2(at)$, $\rho=\sin^2((1-a)t)$, $\Gamma_{HC}=1-2\delta$) there is a smooth function $z(t)$, $0\le t<t_0$, such that
--
--   $$
--   z(t)=b+qt+O(t^2),\qquad \Phi_{bal}(a,t;\delta)=\kappa_H(\delta)-qH_2'(b)\,t+2a(1-a)\,t^2\log_2(1/t)+O(t^2).
--   $$
--
--   The negative linear term dominates the logarithmic entropy cost, which is the mechanism of the strict improvement $\kappa_{HC}<\kappa_H$.
--
--   Differences from the source:
--
--   - reading: 'a smooth function z(t)' with z(t) = b + qt + O(t²) and the O(t²) expansion of Φ_bal → z ∈ C^∞ on [0, t₀) (one-sided at 0) with z(0) = b solving Γ_HC = 1 − 2δ there, and one constant C with both errors ≤ C t² for 0 < t < t₀; reason: the perturbation is for small t ≥ 0 (u, v ≥ 0 in (10)); √η = |sin(at)| makes the boundary equation non-smooth across t = 0; t² log₂(1/t) needs t > 0; O(t²) as t ↓ 0 with constants depending on δ and (a, b)
--   - encoding: H₂′(b) → deriv H2 b; reason: the derivative of H₂, equal to log₂((1 − b)/b) on (0, 1)
-- source:
--   W. Gay, F. Granha Jeronimo, L. Liu, The Honeycomb Framework for Code Bounds, arXiv:2608.20287v2 (sha256 f4b07e318538a352116042dc4da0d4e9d47cfd979cf302c7fce3324584a3cd51), §6.4, Theorem 6.6, eqs. (70)–(72), p.32 (PDF 34)

import Mathlib
import Definitions.Def_HoneycombCodes_kappaHC
import Definitions.Def_HoneycombCodes_kappaBal

set_option autoImplicit false

namespace HoneycombCodes

/-- **Theorem 6.6**, Gay, Granha Jeronimo, Liu, *The Honeycomb Framework for Code Bounds*, arXiv:2608.20287v2 (sha256 f4b07e31…cd51), p.32 (PDF 34). For every `0 < δ < 1/2`,
`κ_HC(δ) ≤ κ_bal(δ) < κ_H(δ)` (70). More precisely, let `(a, b)` be any minimizing whole-cube
point from Lemma 6.2 and put `q := a(1 − a)(1 − P₀)/(1 − 2b) = b(1 − b)/(1 − 2b) > 0`, where
`P₀ = (a − b)(1 − a − b)/(a(1 − a))` (64). On the exact balanced spectral boundary with
`x = a`, `u = at`, `v = (1 − a)t` (71) there is a smooth function `z(t)` such that
`z(t) = b + qt + O(t²)` (72) and
`Φ_bal(a, t; δ) = κ_H(δ) − qH₂′(b)t + 2a(1 − a)t² log₂(1/t) + O(t²)`.

**Formalization Note (reading).** The balanced boundary at `x = a` is
`Γ_HC(a, sin²(at), sin²((1 − a)t), z) = 1 − 2δ` (η = sin²u, ρ = sin²v with u, v ≥ 0, as in (10)).
"Smooth" is `C^∞` on the half-open interval `[0, t₀)` (one-sided at `0`), with `z(0) = b`: the
perturbation is for small `t ≥ 0`, and since `√η = |sin(at)|` the boundary equation is not smooth
across `t = 0`. `O(t²)` means: one constant `C` (depending on δ and
`(a, b)`) with the error at most `C t²` for `0 < t < t₀`; `t² log₂(1/t)` needs `t > 0`. `H₂′` is
`deriv H2`. -/
theorem theorem_6_6 (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    (kappaHC δ ≤ kappaBal δ ∧ kappaBal δ < kappaH δ) ∧
    ∀ a b : ℝ, IsWholeCubeMinimizer δ a b →
      let P₀ : ℝ := (a - b) * (1 - a - b) / (a * (1 - a))
      let q : ℝ := a * (1 - a) * (1 - P₀) / (1 - 2 * b)
      q = b * (1 - b) / (1 - 2 * b) ∧ 0 < q ∧
      ∃ t₀ : ℝ, 0 < t₀ ∧ ∃ zf : ℝ → ℝ,
        ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) zf (Set.Ico 0 t₀) ∧ zf 0 = b ∧
        (∀ t ∈ Set.Ico 0 t₀,
          GammaHC a (Real.sin (a * t) ^ 2) (Real.sin ((1 - a) * t) ^ 2) (zf t) = 1 - 2 * δ) ∧
        ∃ C : ℝ, ∀ t ∈ Set.Ioo 0 t₀,
          |zf t - (b + q * t)| ≤ C * t ^ 2 ∧
          |PhiBal a t δ - (kappaH δ - q * deriv H2 b * t +
              2 * a * (1 - a) * t ^ 2 * Real.logb 2 (1 / t))| ≤ C * t ^ 2 := by sorry

end HoneycombCodes
