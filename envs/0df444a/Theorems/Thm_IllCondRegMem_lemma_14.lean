-- Prove2me | Theorems.Thm_IllCondRegMem_lemma_14
-- name    : IllCondRegMem.lemma_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:56:53.991751+00:00
-- url     : https://prove2.me/theorems/ba0cadb9-dd6d-4765-be10-09af1181dc13
-- title:
--   Lemma 14 — translations of the averaged kernel: $\|K_n-K_n(\cdot-z)\|_1\le Ch(r_0R^2+R+nR\log(e+r_0/h))$, and $\mathbb E_Z\|f_Z-f_Z*K_n\|_1\le A_n$
-- statement:
--   Let $K_n$ be the averaged kernel on $\mathbb R^n$ (density (22)) built from $\phi$ with parameters $R,r_0$.
--
--   1. There is an absolute constant $C>0$ such that for every $n\ge1$, all $R,r_0>0$ and every $z\in\mathbb R^n$ with $h=\|z\|>0$,
--   $$
--   \|K_n-K_n(\cdot-z)\|_1\le Ch\big(r_0R^2+R+nR\log(e+r_0/h)\big).
--   $$
--   2. For the mixtures of Lemma 13 in dimension $n$ (same hypotheses, with $R=C'\sqrt{nL}/\delta$, $r=\delta/2$, $L=\log(en\max\{1,\nu\}/\delta)$ and absolute constants $C',C$), every mixture has a density $f_z$ and
--   $$
--   \mathbb E_Z\|f_Z-f_Z*K_n\|_1\le A_n=C^n\nu^{n/2}\delta^{d_0-n/2}L^{(n-d_0)/2}.
--   $$
--   The first bound makes the smoothed densities stable under small shifts; the second transfers Lemma 13 from one direction to the average over all directions.
--
--   **Formalization Note** $\|\cdot\|_1$ and $\mathbb E_Z$ are lower Lebesgue integrals; the conventions of part 2 are those of Lemma 13.
--
--   Differences from the source:
--   - generalization: (19) with "r₀, R as above" → every n ≥ 1 and all R, r₀ > 0; reason: the proof uses only Lemma 12's envelope (7), valid for all R and r₀ = δ/2 with δ > 0 arbitrary; specializes to the paper's R, r₀
--   - encoding: K_n defined by averaging ϕ(t) dt over lines → K_n defined by its explicit density (22); reason: the paper derives (22) from the averaging definition
--   - reading: A_n, the bound of (12) with ambient dimension n → ∃ C′, C with R = C′√(nL)/δ and L = log(e·n·max{1,ν}/δ); reason: the constants of (12) are existential; L as read in Lemma 13
--   - encoding: mixtures, densities, E_Z, ‖·‖₁ → as in Lemma 13 (measurable random matrices, a.s. (11), ν > 0, absolute continuity in the conclusion, lower integrals); reason: Lean representation
-- source:
--   M. Blanchard, D. Hansen, A. Jayant, V. Sharan, Polynomial Memory-Sample Separations in Non-i.i.d. Ill-Conditioned Regression, STOC 2027 submission (held version, sha256 6369d09f…), Lemma 14, p.15 (PDF p.16); eq. (22), p.16 (PDF p.17)

import Mathlib
import Definitions.Def_IllCondRegMem_gaussMixture
import Definitions.Def_IllCondRegMem_IsPrunedCov
import Definitions.Def_IllCondRegMem_avgKernel

open MeasureTheory ProbabilityTheory Matrix

namespace IllCondRegMem

/-- **Lemma 14 (Translations of the averaged kernel).**
Blanchard, Hansen, Jayant, Sharan, *Polynomial Memory-Sample Separations in Non-i.i.d.
Ill-Conditioned Regression*, STOC 2027 submission (held version, sha256 6369d09f…), Lemma 14,
p.15: "Let K_n be the signed measure obtained by averaging the measures ϕ(t) dt on the lines ℝu
over u ∼ Unif(S^{n−1}), with r₀, R as above. For h = ‖z‖ > 0,
‖K_n − K_n(· − z)‖₁ ≤ Ch(r₀R² + R + nR log(e + r₀/h)). (19) Also, for the mixtures in Lemma 13 in
dimension n, E_Z‖f_Z − f_Z ∗ K_n‖₁ ≤ A_n, (20) where A_n denotes the bound in Eq. (12) with
ambient dimension n."

**Formalization Note.** `K_n` is its explicit density (22) (`avgKernel`). Part (19) is stated
for every dimension `n ≥ 1` and all `R, r₀ > 0` (the kernel `ϕ` with parameters `R, r₀`), with
one absolute `C`. Part (20) is stated under the hypotheses of Lemma 13 in dimension `n`, with
`R = C′√(nL)/δ`, `r = δ/2`, `L = log(e·n·max{1, ν}/δ)`, and absolute constants `C′, C` as in
(12); the conventions (densities, `L¹` norms, `E_Z`) are those of Lemma 13. -/
theorem lemma_14 :
    (∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (R r₀ : ℝ) (z : Vec n), 1 ≤ n → 0 < R → 0 < r₀ → 0 < ‖z‖ →
      l1Dist (avgKernel n R r₀) (fun x => avgKernel n R r₀ (x - z)) ≤
        ENNReal.ofReal (C * ‖z‖ * (r₀ * R ^ 2 + R + n * R * Real.log (Real.exp 1 + r₀ / ‖z‖)))) ∧
    (∃ C' : ℝ, 0 < C' ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (n d₀ m : ℕ) (δ ν : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (Sig : Ω → Matrix (Fin n) (Fin n) ℝ)
        (B : Ω → Matrix (Fin n) (Fin m) ℝ),
        2 ≤ n → (n : ℝ) / 2 + 1 ≤ d₀ → d₀ ≤ n → 0 < δ → δ ≤ 1 → 0 < ν →
        IsRandomMatrix Sig → IsRandomMatrix B → IsPrunedCov P Sig d₀ δ →
        (∀ᵐ ω ∂P, (Sig ω).PosSemidef ∧
          ((ν ^ 2) • (1 : Matrix (Fin n) (Fin n) ℝ) - (Sig ω + B ω * (B ω)ᵀ)).PosSemidef) →
        (∀ z : Vec m, mixtureAt P Sig B z ≪ volume) ∧
        (∫⁻ z, l1Dist (density (mixtureAt P Sig B z))
            (kconv (density (mixtureAt P Sig B z))
              (avgKernel n (C' * Real.sqrt (n * Real.log (Real.exp 1 * n * max 1 ν / δ)) / δ)
                (δ / 2))) ∂(stdGaussian (Vec m))) ≤
          ENNReal.ofReal (C ^ n * ν ^ ((n : ℝ) / 2) * δ ^ ((d₀ : ℝ) - n / 2) *
            Real.log (Real.exp 1 * n * max 1 ν / δ) ^ (((n : ℝ) - d₀) / 2))) := by sorry

end IllCondRegMem
