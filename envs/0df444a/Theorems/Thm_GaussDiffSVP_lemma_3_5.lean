-- Prove2me | Theorems.Thm_GaussDiffSVP_lemma_3_5
-- name    : GaussDiffSVP.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:59:13.363125+00:00
-- url     : https://prove2.me/theorems/963a9826-a45f-418d-89d2-439377f34e4e
-- title:
--   Lemma 3.5 — $\sum_{w\ne0}(H-c\xi_w)_+^{n/2}\le\mathrm{poly}(n)2^{\kappa_{\mathrm{pack}}n}(H^2/4c)^{n/2}$
-- statement:
--   Fix $R_0\ge1$ and set $\xi_w = \|w\|^2/\lambda_1(L)^2$. Uniformly for positive $H,c$ with $H/c\le R_0^2$, for every full-rank lattice $L\subset\mathbb R^n$,
--   $$\sum_{w\in L\setminus\{0\}}(H-c\xi_w)_+^{n/2}\le \mathrm{poly}(n)\,2^{\kappa_{\mathrm{pack}}n}\Big(\frac{H^2}{4c}\Big)^{n/2},$$
--   where $\kappa_{\mathrm{pack}} = 401/1000$ and the polynomial depends only on $R_0$. It is the weighted form of Lemma 3.4 used to bound collisions in the coset count.
--
--   Differences from the source:
--   - reading: $\mathrm{poly}(n)$ depending only on $R_0$ → $C(n+1)^k$ with $C,k$ depending only on $R_0$, for every $n$; reason: the printed lemma has no large-$n$ clause
--   - encoding: $(\cdot)_+^{n/2}$, the sum → $\max(\cdot,0)$ to the real power $n/2$; a sum in $[0,\infty]$; reason: nonnegative terms
--   - encoding: full-rank lattice $L$ → $L = B\mathbb Z^n$, $\det B\ne0$; reason: same instances
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), Lemma 3.5, p.21

import Mathlib
import Definitions.Def_SuperlatSVP_lat

open SuperlatSVP
open scoped ENNReal

namespace GaussDiffSVP

/-- Lemma 3.5 (Gao–Han–Hu, *Gaussian Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), p.21). For fixed `R₀ ≥ 1`, set `ξ_w = ‖w‖²/λ₁(L)²`. Uniformly for positive
`H, c` with `H/c ≤ R₀²`,
`∑_{w ∈ L∖{0}} (H − cξ_w)_+^{n/2} ≤ poly(n) 2^{κ_pack n} (H²/(4c))^{n/2}`,
where the polynomial depends only on `R₀`; `κ_pack = 401/1000`.

**Formalization Note.** "poly(n)" is `C(n + 1)^k` with `C` and `k` depending only on `R₀`, and the
bound is stated for every `n` and every full-rank lattice `L = Bℤⁿ`, as printed (no "large n").
The sum of nonnegative terms is in `ℝ≥0∞`; `(·)_+^{n/2}` is `max(·, 0)` to the real power `n/2`. -/
theorem lemma_3_5 :
    ∀ R₀ : ℝ, 1 ≤ R₀ → ∃ C : ℝ, ∃ k : ℕ, ∀ n : ℕ,
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B.det ≠ 0 → ∀ H c : ℝ, 0 < H → 0 < c → H / c ≤ R₀ ^ 2 →
        ∑' w : {w : E n // w ∈ lat B ∧ w ≠ 0},
            ENNReal.ofReal ((max (H - c * (‖(w : E n)‖ ^ 2 / lam1 (lat B) ^ 2)) 0) ^
              ((n : ℝ) / 2)) ≤
          ENNReal.ofReal (C * ((n : ℝ) + 1) ^ k * (2 : ℝ) ^ ((401 / 1000 : ℝ) * n) *
            (H ^ 2 / (4 * c)) ^ ((n : ℝ) / 2)) := by sorry

end GaussDiffSVP
