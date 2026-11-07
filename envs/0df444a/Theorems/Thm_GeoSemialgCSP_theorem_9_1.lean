-- Prove2me | Theorems.Thm_GeoSemialgCSP_theorem_9_1
-- name    : GeoSemialgCSP.theorem_9_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:52:00.990862+00:00
-- url     : https://prove2.me/theorems/d7294c6a-936d-4583-a5ca-0d8bd82dac05
-- title:
--   Theorem 9.1 — tensor estimate from an expected-norm bound
-- statement:
--   Fix $k\ge2$, $d_{\mathrm{VC}}\ge1$, $C\ge1$, $b\in(0,1]$ and $0\le\kappa\le1$. Let $Z$ be a random element of a finite set with law $\pi_Z$, let $F$ map it to $\mathcal P_q$, and let $\mu=\mathbb EF(Z)$. Suppose that for every family $\mathcal B$ of subsets of $[q]$ with $\mathrm{VCdim}(\mathcal B)\le d_{\mathrm{VC}}$,
--   $$\mathbb E\Bigl[\max_{B\in\mathcal B}F_B(Z)\Bigr]\ \le\ C\Bigl(\max_{B\in\mathcal B}\mu(B)\Bigr)^b+\kappa .$$
--   Set $A=1+C$ and $c=b/(1+b)$. Then for every $\Delta\subseteq[q]^k$ with $\mathrm{fVC}(\Delta)\le d_{\mathrm{VC}}$ and every joint distribution of $Z_1,\dots,Z_k$ each with law $\pi_Z$,
--   $$\mathbb E\,\Delta[F(Z_1),\dots,F(Z_k)]\ \le\ A^{k-1}\bigl[\mu^{\otimes k}(\Delta)\bigr]^{c^{k-1}}+(k-1)A^{k-1}\kappa^{c^{k-2}} .$$
--
--   Correlated queries hit an exceptional relation of bounded fiber VC-dimension about as rarely as independent ones.
--
--   Differences from the source:
--   - generalization: Z, Z₁, …, Z_k on [M]^R with a prescribed common marginal → Z on any finite type Ω with any law πZ; reason: [M]^R with any law is a case; the paper says the estimate permits any common marginal (p.27)
--   - encoding: max over an empty family = 0; powers t^b → real ⨆ B ∈ 𝓑 (0 for empty 𝓑); Real.rpow; reason: the paper's convention (p.27); values are nonnegative so the junk 0 off 𝓑 changes nothing
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), Theorem 9.1, p.27 (PDF p.28)

import Mathlib
import Definitions.Def_GeoSemialgCSP_vcSets
import Definitions.Def_GeoSemialgCSP_fVC
import Definitions.Def_GeoSemialgCSP_massB
import Definitions.Def_GeoSemialgCSP_multilin

namespace GeoSemialgCSP

/-- **Theorem 9.1 (tensor estimate from an expected-norm bound).** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), Theorem 9.1, printed p.27
(PDF p.28): fix `k ≥ 2`, `d_VC ≥ 1`, `C ≥ 1`, `b ∈ (0,1]`, `0 ≤ κ ≤ 1`. Suppose that for every
family `𝓑` with `VCdim(𝓑) ≤ d_VC`, `E‖F_𝓑(Z)‖_∞ ≤ C‖E F_𝓑(Z)‖_∞^b + κ`, where
`‖E F_𝓑(Z)‖_∞ = max_{B ∈ 𝓑} μ(B)`. With `A = 1 + C` and `c = b/(1+b)`, for every `Δ ⊆ [q]^k` with
`fVC(Δ) ≤ d_VC` and every joint distribution of `Z₁, …, Z_k` with the common marginal of `Z`,
`E Δ[F(Z₁), …, F(Z_k)] ≤ A^{k−1}[μ^{⊗k}(Δ)]^{c^{k−1}} + (k−1)A^{k−1}κ^{c^{k−2}}`.

**Formalization Note.** The space of `Z` is any finite type `Ω` with law `πZ` (the paper's
`[M]^R` with any common marginal, p.27); `μ = E F(Z)`. Maxima over a family are real `⨆ B ∈ 𝓑`
(`0` on the empty family, the paper's convention). Exponents are `Real.rpow`. -/
theorem theorem_9_1 (k dVC : ℕ) (hk : 2 ≤ k) (hd : 1 ≤ dVC) (C b κ : ℝ) (hC : 1 ≤ C)
    (hb0 : 0 < b) (hb1 : b ≤ 1) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (Ω : Type) [Fintype Ω] (πZ : PMF Ω) (q : ℕ) (F : Ω → Fin q → ℝ)
    (hF : ∀ ω, F ω ∈ stdSimplex ℝ (Fin q))
    (hnorm : ∀ 𝓑 : Set (Set (Fin q)), vcSets 𝓑 ≤ (dVC : ℕ∞) →
      ∑ ω, (πZ ω).toReal * (⨆ B ∈ 𝓑, massB (F ω) B) ≤
        C * (⨆ B ∈ 𝓑, massB (fun a => ∑ ω, (πZ ω).toReal * F ω a) B) ^ b + κ)
    (Δ : Set (Fin k → Fin q)) (hΔ : fVC Δ ≤ (dVC : ℕ∞))
    (π : PMF (Fin k → Ω)) (hπ : ∀ j, π.map (fun Z => Z j) = πZ) :
    ∑ Z, (π Z).toReal * multilin (Δ.indicator 1) (fun j => F (Z j)) ≤
      (1 + C) ^ (k - 1) *
          (multilin (Δ.indicator 1) (fun _ => fun a => ∑ ω, (πZ ω).toReal * F ω a)) ^
            ((b / (1 + b)) ^ (k - 1)) +
        ((k : ℝ) - 1) * (1 + C) ^ (k - 1) * κ ^ ((b / (1 + b)) ^ (k - 2)) := by sorry

end GeoSemialgCSP
