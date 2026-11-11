-- Prove2me | Theorems.Thm_IllCondRegMem_lemma_13
-- name    : IllCondRegMem.lemma_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:56:56.567739+00:00
-- url     : https://prove2.me/theorems/2727bd35-6796-45a0-a454-319d31e5e532
-- title:
--   Lemma 13 — directional smoothing: $\mathbb E_Z\|f_Z-f_Z^u\|_1\le C^d\nu^{d/2}\delta^{d_0-d/2}L^{(d-d_0)/2}$
-- statement:
--   There are absolute constants $C',C>0$ such that the following holds. Let $d\ge2$, $d/2+1\le d_0\le d$, $\delta=\delta_{\max}\in(0,1]$ and $\nu>0$. Let $(\Sigma,B)$ be random matrices ($d\times d$ and $d\times m$) such that $\Sigma$ is $(d_0,\delta)$-pruned (Definition 11) and, almost surely,
--   $$
--   0\preceq\Sigma,\qquad \Sigma+BB^\top\preceq\nu^2I .
--   $$
--   Let $Z\sim\mathcal N(0,I_m)$ be independent of $(\Sigma,B)$. Then for every $z$ the mixture $\mathbb E_{\Sigma,B}[\mathcal N(Bz,\Sigma)]$ has a density $f_z$, and for every unit vector $u$, with
--   $$
--   L=\log\frac{ed\max\{1,\nu\}}{\delta},\qquad R=\frac{C'\sqrt{dL}}{\delta},\qquad r=\frac\delta2,
--   $$
--   the directional convolution $f^u_z$ of eq. (10) satisfies
--   $$
--   \mathbb E_Z\|f_Z-f_Z^u\|_1\le C^d\nu^{d/2}\delta^{d_0-d/2}L^{(d-d_0)/2}=:A_d .
--   $$
--   Removing high frequencies along one direction changes a pruned Gaussian mixture little; averaged over directions this gives the masking lemma.
--
--   **Formalization Note** $(\Sigma,B)$ are measurable on a probability space; $f_z$ is the Radon–Nikodym derivative; $\mathbb E_Z$ and $\|\cdot\|_1$ are lower Lebesgue integrals.
--
--   Differences from the source:
--   - reading: L := log(ed max{1, ν}/δ, printed with an unbalanced parenthesis under one fraction bar → L = log(e·d·max{1,ν}/δ); reason: the paper applies Lemma 13 with log(enν/δ_max) ≤ CL (proof of Lemma 5, p.18), which fixes this form
--   - reading: direction u of f^u not quantified in the lemma → every unit vector u; reason: eq. (10) and the text before Lemma 12 take any u ∈ S^{d−1}
--   - encoding: random matrices (Σ, B), Z of the appropriate dimension, (11), ν → measurable Σ (d×d), B (d×m, m arbitrary) on a probability space, (11) almost surely, ν > 0; reason: Lean representation; ν = 0 is incompatible with pruning
--   - encoding: f_z denotes the density of the mixture → absolute continuity of every mixture is part of the conclusion; f_z = Radon–Nikodym derivative; reason: the density exists by the proof (L² Fourier transform); stating it makes f_z genuine
--   - encoding: constants C′, C → absolute constants chosen before all data; reason: Lean quantifier order
-- source:
--   M. Blanchard, D. Hansen, A. Jayant, V. Sharan, Polynomial Memory-Sample Separations in Non-i.i.d. Ill-Conditioned Regression, STOC 2027 submission (held version, sha256 6369d09f…), Lemma 13, p.12 (PDF p.13)

import Mathlib
import Definitions.Def_IllCondRegMem_gaussMixture
import Definitions.Def_IllCondRegMem_IsPrunedCov
import Definitions.Def_IllCondRegMem_dirSmooth

open MeasureTheory ProbabilityTheory Matrix

namespace IllCondRegMem

/-- **Lemma 13 (Directional smoothing).**
Blanchard, Hansen, Jayant, Sharan, *Polynomial Memory-Sample Separations in Non-i.i.d.
Ill-Conditioned Regression*, STOC 2027 submission (held version, sha256 6369d09f…), Lemma 13,
p.12: "Fix d ≥ 2, d/2 + 1 ≤ d₀ ≤ d, and δ := δ_max ∈ (0, 1]. Let (Σ, B) be random matrices such
that Σ is (d₀, δ)-pruned and 0 ⪯ Σ, Σ + BBᵀ ⪯ ν²I. (11) Let Z be a standard Gaussian vector of
the appropriate dimension, independent of (Σ, B), and let f_z denote the density of the mixture
E_{Σ,B}[N(Bz, Σ)]. Then for L := log(ed max{1, ν}/δ), R = C′√(dL)/δ, r = δ/2, it holds that
E_Z‖f_Z − f^u_Z‖₁ ≤ C^d ν^{d/2} δ^{d₀−d/2} L^{(d−d₀)/2} := A_d. (12)"

**Formalization Note.** `C′, C` are absolute constants chosen before all data. `(Σ, B)` are
measurable random matrices (`d × d` and `d × m`, `m` arbitrary) on a probability space;
"(d₀, δ)-pruned" is Definition 11 (`IsPrunedCov`); (11) holds almost surely; `ν > 0` is the scale
in (11); `u` is any unit vector (the direction of the smoothing in eq. (10)). `L` is read as
`log(e·d·max{1, ν}/δ)` (the proof uses `log(ν/δ) ≤ L` and `e^{−L} ≤ δ`). That each mixture
`E_{Σ,B}[N(Bz, Σ)]` has a density (is absolutely continuous) is part of the conclusion; `f_z` is
its Radon–Nikodym derivative, `f^u` the directional convolution of eq. (10) with the kernel of
eq. (6) at `(R, r)`, `‖·‖₁` the Lebesgue `L¹` norm and `E_Z` a lower integral against
`Z ∼ N(0, I_m)`. -/
theorem lemma_13 :
    ∃ C' : ℝ, 0 < C' ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (d d₀ m : ℕ) (δ ν : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (Sig : Ω → Matrix (Fin d) (Fin d) ℝ)
        (B : Ω → Matrix (Fin d) (Fin m) ℝ) (u : Vec d),
        2 ≤ d → (d : ℝ) / 2 + 1 ≤ d₀ → d₀ ≤ d → 0 < δ → δ ≤ 1 → 0 < ν →
        IsRandomMatrix Sig → IsRandomMatrix B → IsPrunedCov P Sig d₀ δ →
        (∀ᵐ ω ∂P, (Sig ω).PosSemidef ∧
          ((ν ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ) - (Sig ω + B ω * (B ω)ᵀ)).PosSemidef) →
        ‖u‖ = 1 →
        (∀ z : Vec m, mixtureAt P Sig B z ≪ volume) ∧
        (∫⁻ z, l1Dist (density (mixtureAt P Sig B z))
            (dirSmooth (C' * Real.sqrt (d * Real.log (Real.exp 1 * d * max 1 ν / δ)) / δ) (δ / 2)
              (density (mixtureAt P Sig B z)) u) ∂(stdGaussian (Vec m))) ≤
          ENNReal.ofReal (C ^ d * ν ^ ((d : ℝ) / 2) * δ ^ ((d₀ : ℝ) - d / 2) *
            Real.log (Real.exp 1 * d * max 1 ν / δ) ^ (((d : ℝ) - d₀) / 2)) := by sorry

end IllCondRegMem
