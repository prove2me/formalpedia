-- Prove2me | Theorems.Thm_OnlineBeckFiala_lemma_2_5
-- name    : OnlineBeckFiala.lemma_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:34:04.438206+00:00
-- url     : https://prove2.me/theorems/0869618a-2b64-441b-a503-dfe1467406f7
-- title:
--   Lemma 2.5 (Curvature criterion) — $D_v(x)\le2\log2$ implies $x$ is $v$-balanced
-- statement:
--   Let $u:\mathbb R\to\mathbb R$ be a potential with $e^{-u}$ integrable on $(-1,1)$, let $L$ be real, and let $\mu(x)=(LZ)^{-n}\exp(-\sum_iu(x_i/L))$ on $(-L,L)^n$ and $0$ off it, with $Z=\int_{-1}^1e^{-u}$. If $x,v\in\mathbb R^n$ satisfy $x+v\in(-L,L)^n$, $x-v\in(-L,L)^n$ and
--   $$D_v(x)=\Delta^+(x,v)+\Delta^-(x,v)\le2\log2,$$
--   then $x$ is $v$-balanced: $x\in(-L,L)^n$ and $p^+_v(x)+p^-_v(x)\ge\tfrac13$.
--
--   This converts a bound on the second-order variation of the potential into balance, which is what the potential of §3 is built to control.
--
--   **Formalization Note** The potential is real-valued; the paper's $u=+\infty$ off $(-1,1)$ is encoded by the indicator in the density. That $x$ lies in the cube follows from $x\pm v$ lying in the convex cube.
--
--   Differences from the source:
--   - encoding: ρ = (LZ)⁻¹e^{−u(x/L)} is a probability density, u = +∞ off (−1, 1) → u real-valued, e^{−u} integrable on (−1, 1), density zero off the cube by an indicator; reason: integrability is the Lean form of Z < ∞ (without it the Bochner integral Z is 0); u is never read off (−1, 1)
-- source:
--   Altschuler, Tikhomirov, Online Beck–Fiala Down to Logarithmic Sparsity, arXiv:2607.14238 (held version, sha256 5a1529d2…), p.4, Lemma 2.5

import Mathlib
import Definitions.Def_OnlineBeckFiala_IsBalanced

open MeasureTheory

namespace OnlineBeckFiala

/-- **Lemma 2.5 (Curvature criterion), p.4.** Altschuler, Tikhomirov, *Online Beck–Fiala Down to
Logarithmic Sparsity*, arXiv:2607.14238 (held version, sha256 5a1529d2…): "If x + v ∈ (−L, L)^n,
x − v ∈ (−L, L)^n, and Dv(x) ≤ 2 log 2, then x is v-balanced."

Setting of §2.1, p.3: `µ(x) = (LZ)^{−n} exp(−∑ u(x_i/L))` on the cube, with `Z = ∫_{−1}^1 e^{−u}`.

**Formalization Note.** `u : ℝ → ℝ` is real-valued on `(−1, 1)` (the paper's `u = +∞` off it is
encoded by the density's indicator). "ρ is a probability density" is encoded by integrability of
`e^{−u}` on `(−1, 1)`; without it the Lean integral `Z` would be `0`. That `x` lies in the cube, as
Definition 2.3 requires, follows from `x ± v` in the (convex) cube. -/
theorem lemma_2_5 {n : ℕ} (u : ℝ → ℝ) (L : ℝ)
    (hu : IntegrableOn (fun y => Real.exp (-u y)) (Set.Ioo (-1) 1))
    (x v : Fin n → ℝ) (hplus : x + v ∈ cube L) (hminus : x - v ∈ cube L)
    (hD : Dv u L x v ≤ 2 * Real.log 2) :
    IsBalanced L (uDensity u L) v x := by sorry

end OnlineBeckFiala
