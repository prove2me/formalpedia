-- Prove2me | Theorems.Thm_FractionalSpectralGP_vage_inequality
-- name    : FractionalSpectralGP.vage_inequality
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:26:25.713367+00:00
-- url     : https://prove2.me/theorems/71942f35-9fbf-4686-8b7f-c721efa8140c
-- title:
--   §4, (4.7)–(4.8) — Våge's inequality $\|h\diamond u\|_k\le A(k-l)\|h\|_l\|u\|_k$
-- statement:
--   Let $l,k\in\mathbb N_0$ with $k>l+1$. Then
--
--   $$
--   A(k-l)=\Big(\sum_{\alpha\in\ell}(2\mathbb N)^{(l-k)\alpha}\Big)^{1/2}<\infty, \tag{4.8}
--   $$
--
--   and for every $h\in\mathcal H'_l$ and $u\in\mathcal H'_k$ the Wick product $h\diamond u$ lies in $\mathcal H'_k$ with
--
--   $$
--   \|h\diamond u\|_k\le A(k-l)\,\|h\|_l\,\|u\|_k . \tag{4.7}
--   $$
--
--   Våge's inequality is what makes the Wick product stable in $S_{-1}$; in Theorem 7.1 it is applied with $l=0$ to $Y(t)\diamond W_\sigma(t)$.
--
--   Differences from the source:
--   - encoding: formal series Σ f_α H_α and the norm ‖·‖_k of H′_k → coefficient families ℓ → ℂ and the ℓ²-norm of (f_α (2ℕ)^{−kα/2}); reason: the defining isometry of H′_k; same objects
--   - encoding: multi-indices α = (α_1, α_2, …) with weight 2k at coordinate k → α : ℕ →₀ ℕ, coordinate n carries Z_n and weight 2(n + 1); reason: index shift k = n + 1; same objects
--   - reading: (4.7) with A(k − l) given by the series (4.8) → the convergence of (4.8) and h ♦ u ∈ H′_k are asserted as conclusions; reason: the inequality presupposes both; asserting them excludes junk values
--   - generalization: l, k natural numbers → l, k ∈ ℕ₀ (l = 0 allowed); reason: the cited Proposition 3.3.2 allows l = 0, and STEP 2 of Theorem 7.1 applies (4.7) with l = 0; l ≥ 1 is a special case
-- source:
--   Alpay, Jorgensen, Levanony, A class of Gaussian processes with fractional spectral measures, arXiv:1009.0233v1, §4, (4.7)–(4.8), p.11 (cited from Holden–Øksendal–Ubøe–Zhang, Proposition 3.3.2)

import Mathlib
import Definitions.Def_FractionalSpectralGP_kondWeight
import Definitions.Def_FractionalSpectralGP_MemHprime
import Definitions.Def_FractionalSpectralGP_embedHprime
import Definitions.Def_FractionalSpectralGP_wick

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped SchwartzMap ENNReal

namespace FractionalSpectralGP

/-- Våge's inequality, §4, (4.7)–(4.8) (Alpay, Jorgensen, Levanony, arXiv:1009.0233v1, p.11; cited from Holden–Øksendal–Ubøe–Zhang,
Proposition 3.3.2): for natural numbers `l, k` with `k > l + 1`, `h ∈ 𝓗'_l` and `u ∈ 𝓗'_k`,
`‖h ♦ u‖_k ≤ A(k − l) ‖h‖_l ‖u‖_k` with `A(k − l) = (Σ_α (2ℕ)^{(l−k)α})^{1/2}`.

**Formalization Note.** The statement also asserts that the series defining `A(k − l)` converges
and that `h ♦ u ∈ 𝓗'_k` (both implicit in the page), so neither side is a junk value. `l = 0` is
allowed. -/
theorem vage_inequality (l k : ℕ) (hlk : l + 1 < k) :
    Summable (fun α : ℕ →₀ ℕ => (kondWeight α ^ (k - l))⁻¹) ∧
    ∀ f u : (ℕ →₀ ℕ) → ℂ, MemHprime l f → MemHprime k u →
      MemHprime k (wick f u) ∧
      ‖embedHprime k (wick f u)‖ ≤
        Real.sqrt (∑' α : ℕ →₀ ℕ, (kondWeight α ^ (k - l))⁻¹) *
          ‖embedHprime l f‖ * ‖embedHprime k u‖ := by sorry

end FractionalSpectralGP
