-- Prove2me | Theorems.Thm_LCAntiConc_lemma_4_8
-- name    : LCAntiConc.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:50:00.626031+00:00
-- url     : https://prove2.me/theorems/f6386cfb-df76-4e82-a2f2-b7a5b9d95f5e
-- title:
--   Lemma 4.8 — a distribution on unit vectors with the pseudo-second moments and at most twice the defect
-- statement:
--   Let $B\in\mathbb R^{n\times n}$ be a random symmetric matrix with $\mathbb E\|B\|_{\mathrm{op}}^2<\infty$, and let $\tilde{\mathbb E}$ be a degree-$6$ pseudo-expectation satisfying $\{\|z\|^2=1\}$ over the $n$-dimensional formal variable $z$. There is a probability distribution of unit vectors $u\in\mathbb R^n$ with $\mathbb E\,uu^\top=\tilde{\mathbb E}\,zz^\top$ and
--
--   $$\mathop{\mathbb E}_u\mathop{\mathbb E}_X\Big[u^\top B^2u-\big(u^\top Bu\big)^2\Big]\le2\,\tilde{\mathbb E}\,\mathop{\mathbb E}_X\Big[z^\top B^2z-\big(z^\top Bz\big)^2\Big].$$
--
--   Here $\mathbb E_X$ is the expectation over the randomness of $B$, and on the right $\tilde{\mathbb E}$ is applied to the polynomial in $z$ obtained by taking that expectation coefficientwise.
--
--   This rounding statement is the input to Lemma 4.7.
--
--   **Formalization Note** The randomness of $B$ is a probability space $(\Omega,P)$; the distribution of $u$ is a probability measure on $\mathbb R^n$ giving full mass to the unit sphere, and $\mathbb E\,uu^\top=\tilde{\mathbb E}\,zz^\top$ holds entrywise. The page's dimension $D$ is written $n$.
--
--   Differences from the source:
--   - encoding: random symmetric matrix B → B : Ω → ℝ^{n×n} on a probability space, entrywise measurable, symmetric for every ω; reason: a random variable is measurable; Matrix carries no measurable-space instance in Mathlib
--   - encoding: actual distribution over unit vectors u with 𝔼uuᵀ = Ẽzzᵀ → probability measure ν on ℝ^n with ν(complement of the unit sphere) = 0 and ∫ uᵢuⱼ dν = Ẽ zᵢzⱼ for all i, j; reason: same object
--   - encoding: a degree-D pseudo-expectation, a linear functional on ℝ[v]_{≤D} → a linear functional on all of ℝ[v] constrained only on polynomials of degree ≤ D; reason: its restriction to ℝ[v]_{≤D} is the page's object; the statement applies it only to polynomials of degree ≤ D
-- source:
--   Tiegel, Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions, STOC 2027 submission (manuscript sha256 7164444e…), Lemma 4.8, p.24 (PDF p.26)

import Mathlib
import Definitions.Def_LCAntiConc_IsPseudoExp
import Definitions.Def_LCAntiConc_polyExpect
import Definitions.Def_LCAntiConc_quadForm
import Definitions.Def_LiqPremiaEq_opNorm

namespace LCAntiConc

open MeasureTheory

/-- **Lemma 4.8**. Let `B ∈ ℝ^{n×n}` be a random symmetric matrix with `𝔼‖B‖²_op < ∞`, and let
`Ẽ` be a degree-6 pseudo-expectation satisfying `{‖z‖² = 1}` over the `n`-dimensional formal
variable `z`. There exists an actual distribution over unit vectors `u` with `𝔼 u uᵀ = Ẽ z zᵀ`
and `𝔼_u 𝔼_X[uᵀB²u - (uᵀBu)²] ≤ 2 Ẽ 𝔼_X[zᵀB²z - (zᵀBz)²]`.

Tiegel, *Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions*,
STOC 2027 submission (manuscript sha256 7164444e…), Lemma 4.8, p.24 (PDF p.26).

**Formalization Note** The randomness of `B` (written `X ∈ ℝ^d` with `B = B(X)` on the page) is
an arbitrary probability space `(Ω, P)`, and `B` is a measurable map (entrywise). The page's
dimension `D` is `n`. The distribution over unit vectors is a probability measure on `ℝ^n`
giving full mass to the unit sphere; `𝔼 uuᵀ = Ẽ zzᵀ` is entrywise. The right-hand side applies
`Ẽ` to the expectation polynomial of `zᵀB²z - (zᵀBz)²`. -/
theorem lemma_4_8 (n : ℕ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hB : ∀ i j, Measurable fun ω => B ω i j) (hsymm : ∀ ω, (B ω).IsSymm)
    (hint : Integrable (fun ω => LiqPremiaEq.opNorm (B ω) ^ 2) P)
    (L : MvPolynomial (Fin n) ℝ →ₗ[ℝ] ℝ) (hL : IsPseudoExp 6 L) :
    ∃ ν : Measure (EuclideanSpace ℝ (Fin n)), IsProbabilityMeasure ν ∧
      ν {u | ‖u‖ = 1}ᶜ = 0 ∧
      (∀ i j, ∫ u, u i * u j ∂ν = L (MvPolynomial.X i * MvPolynomial.X j)) ∧
      ∫ u, ∫ ω, ((∑ i, ∑ j, u i * (B ω ^ 2) i j * u j) -
          (∑ i, ∑ j, u i * B ω i j * u j) ^ 2) ∂P ∂ν ≤
        2 * L (polyExpect P (fun ω => quadForm (B ω ^ 2) - quadForm (B ω) ^ 2)) := by sorry

end LCAntiConc
