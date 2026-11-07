-- Prove2me | Theorems.Thm_GeoSemialgCSP_lemma_5_4
-- name    : GeoSemialgCSP.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:52:11.682092+00:00
-- url     : https://prove2.me/theorems/22b0c479-608e-44f4-94d4-2423dc597e85
-- title:
--   Lemma 5.4 — a bounded list of influential coordinates
-- statement:
--   Let $d_{\mathrm{VC}}\in\mathbb N$, $0<\rho<1$ and $\tau_0\in(0,1]$. There is a constant $B_{\mathrm{list}}=B_{\mathrm{list}}(d_{\mathrm{VC}},\rho,\tau_0)$ such that for every family $\mathcal C$ of regions with VC-dimension at most $d_{\mathrm{VC}}$, every alphabet $[M]$, every $R$ and every fractional solution $\xi$ on $[M]^R$ (with any finite output support),
--   $$\Bigl|\Bigl\{r:\ \sup_{A\in\mathcal C}\mathrm{Inf}_r(T_\rho\,\xi_A)\ge\tau_0\Bigr\}\Bigr|\ \le\ B_{\mathrm{list}} .$$
--   The bound is independent of $M$, $R$ and the output support.
--
--   The lemma bounds the list of candidate labels in the Unique Games decoding, simultaneously for all regions.
--
--   Differences from the source:
--   - generalization: regions C of the domain X and output points in X → regions in an arbitrary type U and output points x : Fin n → U; reason: U = ℝ^d with points in X is a case
--   - encoding: the alphabet [M], M ≥ 1 → any nonempty finite type W; reason: W ≅ Fin |W|; τ may depend on M, and so on W
--   - encoding: ρ (keep probability) → σ; reason: renaming
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), Lemma 5.4, p.16 (PDF p.17)

import Mathlib
import Definitions.Def_GeoSemialgCSP_vcSets
import Definitions.Def_GeoSemialgCSP_infl
import Definitions.Def_GeoSemialgCSP_noiseOp
import Definitions.Def_GeoSemialgCSP_regMass
open Classical

namespace GeoSemialgCSP

/-- **Lemma 5.4 (a bounded list of influential coordinates).** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), Lemma 5.4, printed p.16 (PDF
p.17): let `C` have VC-dimension at most `d_VC`, `0 < ρ < 1`, `τ₀ ∈ (0,1]`. There is
`B_list = B_list(d_VC, ρ, τ₀)` such that for every fractional solution `ξ` on `[M]^R`,
`|{r : sup_{S ∈ C} Inf_r(T_ρ ξ_S) ≥ τ₀}| ≤ B_list`, independently of `M`, `R` and the output
support.

**Formalization Note.** `ρ` (here `σ`) is the keep probability. Regions live in an arbitrary type
`U` and `ξ` has finitely many output points `x₁, …, x_n ∈ U`; `[M]` is any nonempty finite type
`W`. `B_list` is chosen before `U, C, W, R, n, x`. The supremum is the real `⨆ A ∈ C`: the values are
in `[0, 1/4]`, and the junk `0` off `C` is harmless. -/
theorem lemma_5_4 (dVC : ℕ) (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1) (τ₀ : ℝ) (hτ0 : 0 < τ₀)
    (hτ1 : τ₀ ≤ 1) :
    ∃ Blist : ℕ, ∀ (U : Type) (C : Set (Set U)), vcSets C ≤ (dVC : ℕ∞) →
      ∀ (W : Type) [Fintype W] [Nonempty W] (R n : ℕ) (x : Fin n → U)
        (G : (Fin R → W) → Fin n → ℝ), (∀ z, G z ∈ stdSimplex ℝ (Fin n)) →
        ((Finset.univ : Finset (Fin R)).filter
          (fun r => τ₀ ≤ ⨆ A ∈ C, infl (noiseOp σ (regMass x G A)) r)).card ≤ Blist := by sorry

end GeoSemialgCSP
