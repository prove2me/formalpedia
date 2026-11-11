-- Prove2me | Theorems.Thm_HermiteLaptop_MaxAgree_lemma_3_4
-- name    : HermiteLaptop.MaxAgree.lemma_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:18:43.166898+00:00
-- url     : https://prove2.me/theorems/54324264-4a52-44d1-85c4-f1de443d2918
-- title:
--   Lemma 3.4 — Gaussian tail bound |T^{(R)}_{a,λ}| ≤ 2(2π)^{−(r(λ)+1)/2} Σ_j |s_j| G_j(r(λ)+1, R), with the G_j recurrence
-- statement:
--   Write $S_{a,\lambda}(x)=\sum_{j=0}^Ds_jx^j$ with $D$ its degree. For every $a$, $\lambda$ and every $R>0$,
--   $$\big|T^{(R)}_{a,\lambda}\big|\le2(2\pi)^{-(r(\lambda)+1)/2}\sum_{j=0}^D|s_j|\,G_j(r(\lambda)+1,R).\tag{19}$$
--   Moreover, for $\mu>0$ and $R>0$,
--   $$G_0(\mu,R)\le\frac{e^{-\mu R^2/2}}{\mu R},\qquad G_1(\mu,R)=\frac{e^{-\mu R^2/2}}{\mu},\qquad G_j(\mu,R)=\frac{R^{j-1}e^{-\mu R^2/2}}{\mu}+\frac{j-1}{\mu}G_{j-2}(\mu,R)\ \ (j\ge2).\tag{20}$$
--   These are the explicit tail bounds that, combined with validated quadrature on $[-R,R]$, enclose each $B_{a,\lambda}$ in a rational interval.
--
--   **Formalization Note.** $D$ is `natDegree` and $s_j$ is `coeff j` of `Spoly a λ`; the exponent is a real power.
--
--   Differences from the source:
--   - generalization: λ a multiset of k−1 naturals for some k ≥ 2 → λ any finite multiset of naturals (also the empty one); reason: the bound holds for every multiset; the source sizes are included
--   - encoding: (20) for the G_j with μ > 0, R > 0 → a separate universally quantified clause over μ > 0, R′ > 0; reason: the "Moreover" part is a statement about G_j alone
-- source:
--   García-Soriano, Miyauchi, Hermite Brings a Laptop, arXiv:2609.35453 (held version, sha256 97504f90…), p. 21 (PDF 24), Lemma 3.4

import Mathlib
import Definitions.Def_HermiteLaptop_MaxAgree_OneDim

namespace HermiteLaptop.MaxAgree

/-- Lemma 3.4: with `S_{a,λ}(x) = Σ_{j=0}^{D} s_j xʲ`, for every `R > 0`
`|T^{(R)}_{a,λ}| ≤ 2(2π)^{−(r(λ)+1)/2} Σ_j |s_j| G_j(r(λ)+1, R)` (19); and (20):
`G_0(μ,R) ≤ e^{−μR²/2}/(μR)`, `G_1(μ,R) = e^{−μR²/2}/μ`,
`G_j(μ,R) = R^{j−1} e^{−μR²/2}/μ + ((j−1)/μ) G_{j−2}(μ,R)` for `j ≥ 2`. -/
theorem lemma_3_4 (a : ℕ) (lam : Multiset ℕ) (R : ℝ) (hR : 0 < R) :
    |tailT R a lam| ≤
      2 * (2 * Real.pi) ^ (-((rCount lam : ℝ) + 1) / 2) *
        ∑ j ∈ Finset.range ((Spoly a lam).natDegree + 1),
          |(Spoly a lam).coeff j| * Gmom j ((rCount lam : ℝ) + 1) R ∧
    ∀ μ : ℝ, 0 < μ → ∀ R' : ℝ, 0 < R' →
      Gmom 0 μ R' ≤ Real.exp (-(μ * R' ^ 2) / 2) / (μ * R') ∧
      Gmom 1 μ R' = Real.exp (-(μ * R' ^ 2) / 2) / μ ∧
      ∀ j : ℕ, 2 ≤ j →
        Gmom j μ R' = R' ^ (j - 1) * Real.exp (-(μ * R' ^ 2) / 2) / μ +
          ((j : ℝ) - 1) / μ * Gmom (j - 2) μ R' := by sorry

end HermiteLaptop.MaxAgree
