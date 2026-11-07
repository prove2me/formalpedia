-- Prove2me | Theorems.Thm_LCAntiConc_lemma_4_7
-- name    : LCAntiConc.lemma_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:51:01.456903+00:00
-- url     : https://prove2.me/theorems/64a860e3-ab0a-48ec-9512-9c018b256aaa
-- title:
--   Lemma 4.7 — a degree-2 partition induced by sums of squares with $\mathbb E_{\mathcal C}\mathbb E_X\mathrm{Var}\,z^\top Bz\le6\,\tilde{\mathbb E}\,\mathbb E_X[z^\top B^2z-(z^\top Bz)^2]$
-- statement:
--   Let $B\in\mathbb R^{n\times n}$ be a random symmetric matrix with $\mathbb E\|B\|_{\mathrm{op}}^2<\infty$, and let $\tilde{\mathbb E}$ be a pseudo-expectation of degree $D\ge10$ satisfying $\{\|z\|^2=1\}$ over the $n$-dimensional formal variable $z$. Then there is a degree-$2$ partition $\mathcal C=\{(p_i,\tilde{\mathbb E}_i)\}$ of $\tilde{\mathbb E}$ with
--
--   $$\mathop{\mathbb E}_{\mathcal C}\mathop{\mathbb E}_X\mathrm{Var}_{\tilde{\mathbb E}_i}\big(z^\top Bz\big)\le6\,\tilde{\mathbb E}\,\mathop{\mathbb E}_X\Big[z^\top B^2z-\big(z^\top Bz\big)^2\Big].$$
--
--   Further, the partition is induced by a collection of sum-of-squares polynomials $\{r_i\}$.
--
--   The induced form is what lets the partition be pulled back through the tensor power $v\mapsto v^{\otimes k}$ in the proof of Lemma 4.6.
--
--   **Formalization Note** The randomness of $B$ is a probability space $(\Omega,P)$. Both clauses of the conclusion are stated.
--
--   Differences from the source:
--   - generalization: X ∈ ℝ^d, B = B(X) ∈ ℝ^{D×D} with D ≥ d → B a measurable random matrix on an arbitrary probability space (Ω, P), no relation between the dimension of z and an auxiliary d; reason: specializes to Ω = ℝ^d with the law of X; the assumption D ≥ d only concerns X, which enters only through the randomness of B
--   - encoding: random matrix → entrywise measurable map; reason: a random variable is measurable; Matrix carries no measurable-space instance in Mathlib
--   - encoding: a degree-D pseudo-expectation, a linear functional on ℝ[v]_{≤D} → a linear functional on all of ℝ[v] constrained only on polynomials of degree ≤ D; reason: its restriction to ℝ[v]_{≤D} is the page's object; the statement applies it only to polynomials of degree ≤ D
-- source:
--   Tiegel, Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions, STOC 2027 submission (manuscript sha256 7164444e…), Lemma 4.7, p.23 (PDF p.25)

import Mathlib
import Definitions.Def_LCAntiConc_IsPseudoExp
import Definitions.Def_LCAntiConc_IsPartition
import Definitions.Def_LCAntiConc_IsInducedBy
import Definitions.Def_LCAntiConc_polyExpect
import Definitions.Def_LCAntiConc_pVar
import Definitions.Def_LCAntiConc_quadForm
import Definitions.Def_LiqPremiaEq_opNorm

namespace LCAntiConc

open MeasureTheory

/-- **Lemma 4.7**. Let `B ∈ ℝ^{n×n}` be a random symmetric matrix with `𝔼‖B‖²_op < ∞`, and let
`Ẽ` be a pseudo-expectation of degree at least 10 satisfying `{‖z‖² = 1}` over the
`n`-dimensional formal variable `z`. Then there exists a degree-2 partition `𝒞 = {(pᵢ, Ẽᵢ)}` with
`𝔼_𝒞 𝔼_X Var_{Ẽᵢ} zᵀBz ≤ 6 Ẽ 𝔼_X[zᵀB²z - (zᵀBz)²]`. Further, the partition is induced by a
collection of sum-of-squares polynomials `{rᵢ}`.

Tiegel, *Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions*,
STOC 2027 submission (manuscript sha256 7164444e…), Lemma 4.7, p.23 (PDF p.25).

**Formalization Note** The randomness of `B` is an arbitrary probability space `(Ω, P)` (the page
writes `B = B(X)` with `X ∈ ℝ^d` and assumes the dimension `n` of `z` satisfies `n ≥ d`; that
assumption only concerns `X`, and is dropped). `B` is measurable entrywise. Both clauses of the
conclusion are stated: the bound and "induced by". -/
theorem lemma_4_7 (n : ℕ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hB : ∀ i j, Measurable fun ω => B ω i j) (hsymm : ∀ ω, (B ω).IsSymm)
    (hint : Integrable (fun ω => LiqPremiaEq.opNorm (B ω) ^ 2) P)
    (D : ℕ) (hD : 10 ≤ D) (L : MvPolynomial (Fin n) ℝ →ₗ[ℝ] ℝ) (hL : IsPseudoExp D L) :
    ∃ (ι : Type) (_ : Fintype ι) (p : ι → ℝ) (Li : ι → MvPolynomial (Fin n) ℝ →ₗ[ℝ] ℝ)
      (ι' : Type) (_ : Fintype ι') (r : ι' → MvPolynomial (Fin n) ℝ) (e : ι → ι'),
      IsPartition D 2 L p Li ∧ IsInducedBy D 2 L p Li r e ∧
      ∑ i, p i * ∫ ω, pVar (Li i) (quadForm (B ω)) ∂P ≤
        6 * L (polyExpect P (fun ω => quadForm (B ω ^ 2) - quadForm (B ω) ^ 2)) := by sorry

end LCAntiConc
