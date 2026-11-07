-- Prove2me | Theorems.Thm_GeoSemialgCSP_corollary_9_2
-- name    : GeoSemialgCSP.corollary_9_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:53:37.067446+00:00
-- url     : https://prove2.me/theorems/f97fc4bb-9d73-432d-8cda-abba78a958eb
-- title:
--   Corollary 9.2 — sampling estimate for smoothed assignments
-- statement:
--   Fix $k\ge2$, $d_{\mathrm{VC}}\ge1$ and $0<\eta<1$. Let $C\ge1$, $b\in(0,1]$ be the constants of Theorem 8.1 (any constants with its norm-bound property), and set $A=1+C$, $c=b/(1+b)$. For every $M,q\ge1$ and every $\delta>0$ there is $\tau=\tau(M,q,k,d_{\mathrm{VC}},\eta,\delta)>0$, independent of $R$, such that
--   $$\mathbb E\,\Delta[F(Z_1),\dots,F(Z_k)]\ \le\ A^{k-1}\bigl[\mu^{\otimes k}(\Delta)\bigr]^{c^{k-1}}+\delta$$
--   whenever $F=T_{1-\eta}G$ for some $G:[M]^R\to\mathcal P_q$, $F$ is $\tau$-pseudorandom, $\mathrm{fVC}(\Delta)\le d_{\mathrm{VC}}$, and $Z_1,\dots,Z_k$ have any joint distribution with each $Z_j$ uniform on $[M]^R$. Here $\mu=\mathbb EF(Z)$ for uniform $Z$.
--
--   This controls the exceptional tuples of Theorem 7.1 on the correlated queries of the dictatorship test.
--
--   Differences from the source:
--   - generalization: let C, b be the constants of Theorem 8.1 → every C ≥ 1, b ∈ (0,1] with the property NormBound of Theorem 8.1 (hypotheses); reason: Theorem 8.1's constants are existential, so the page's C, b are one such pair; the statement for every such pair specializes to it, and the proof uses only that property
--   - encoding: the alphabet [M], M ≥ 1 → any nonempty finite type W; reason: W ≅ Fin |W|; τ may depend on M, and so on W
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), Corollary 9.2, p.28 (PDF p.29)

import Mathlib
import Definitions.Def_GeoSemialgCSP_NormBound
import Definitions.Def_GeoSemialgCSP_noiseOpV
import Definitions.Def_GeoSemialgCSP_inflV
import Definitions.Def_GeoSemialgCSP_fVC
import Definitions.Def_GeoSemialgCSP_multilin
import Definitions.Def_GeoSemialgCSP_unifAvg

namespace GeoSemialgCSP

/-- **Corollary 9.2 (sampling estimate for smoothed assignments).** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), Corollary 9.2, printed
p.28 (PDF p.29): fix `k ≥ 2`, `d_VC ≥ 1`, `0 < η < 1`; let `C, b` be the constants of Theorem 8.1,
`A = 1 + C`, `c = b/(1+b)`. For every `M, q ≥ 1` and `δ > 0` there is `τ > 0`, independent of `R`,
such that `E Δ[F(Z₁), …, F(Z_k)] ≤ A^{k−1}[μ^{⊗k}(Δ)]^{c^{k−1}} + δ` whenever `F = T_{1−η}G` for
some `G : [M]^R → P_q`, `F` is `τ`-pseudorandom, each `Z_j` is uniform on `[M]^R` (any joint law),
and `fVC(Δ) ≤ d_VC`; `μ = E F(Z)` for uniform `Z`.

**Formalization Note.** "The constants of Theorem 8.1" are any constants `C ≥ 1`, `b ∈ (0,1]` with
the property `NormBound d_VC η C b` of Theorem 8.1 (whichever ones Theorem 8.1 supplies).
`[M]` is any nonempty finite type `W`. -/
theorem corollary_9_2 (k dVC : ℕ) (hk : 2 ≤ k) (hd : 1 ≤ dVC) (η : ℝ) (hη0 : 0 < η)
    (hη1 : η < 1) :
    ∀ C b : ℝ, 1 ≤ C → 0 < b → b ≤ 1 → NormBound dVC η C b →
      ∀ (W : Type) [Fintype W] [Nonempty W] (q : ℕ), 1 ≤ q → ∀ δ : ℝ, 0 < δ →
        ∃ τ : ℝ, 0 < τ ∧ ∀ (R : ℕ) (G : (Fin R → W) → Fin q → ℝ),
          (∀ z, G z ∈ stdSimplex ℝ (Fin q)) →
          (∀ r, inflV (noiseOpV (1 - η) G) r ≤ τ) →
          ∀ Δ : Set (Fin k → Fin q), fVC Δ ≤ (dVC : ℕ∞) →
          ∀ π : PMF (Fin k → (Fin R → W)),
            (∀ j, π.map (fun Z => Z j) = PMF.uniformOfFintype (Fin R → W)) →
            ∑ Z, (π Z).toReal * multilin (Δ.indicator 1) (fun j => noiseOpV (1 - η) G (Z j)) ≤
              (1 + C) ^ (k - 1) *
                  (multilin (Δ.indicator 1)
                    (fun _ => fun a => unifAvg (fun z => noiseOpV (1 - η) G z a))) ^
                    ((b / (1 + b)) ^ (k - 1)) + δ := by sorry

end GeoSemialgCSP
