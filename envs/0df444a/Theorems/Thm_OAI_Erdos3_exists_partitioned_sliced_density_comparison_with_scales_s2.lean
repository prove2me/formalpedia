-- Prove2me | Theorems.Thm_OAI_Erdos3_exists_partitioned_sliced_density_comparison_with_scales_s2
-- name    : OAI.Erdos3.exists_partitioned_sliced_density_comparison_with_scales_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:50:10.249252+00:00
-- url     : https://prove2.me/theorems/c393b75e-275f-43a3-8394-7e0b1ab110f2
-- title:
--   With explicit radius and tolerance, the regularized sliced ideal density and the allocated profile jet give integrals within E for every bounded test
-- statement:
--   All named objects below are defined by OpenAI.
--
--   **Data and hypotheses.** Let $\Omega$ be a measurable space and $D, G, Z, \alpha$ finite types ($\alpha$ with decidable equality), $B_d$ ($d \in D$) finite types, $h : D \to \mathbb{N}$ with $h_d > 0$ for all $d$, $P$ a decidable predicate on $D$, and `extra : G → Option α → Z`. For each $d$ with $\neg P(d)$ let $O_d$ be a nonempty finite type, `sets d : O d → Finset α` injective with $|\texttt{sets}\ d\ o| \le h_d$, and `block d : O d → B d` injective. Let $\psi : \mathbb{R} \to \mathbb{R}$ be $C^\infty$ with values in $[0,1]$, $\psi(t) = 0$ for $|t| \le 1$ and $\psi(t) = 1$ for $|t| \ge 2$; let $A, T \in \mathbb{R}_{\ge 0}$ with $\psi$ $A$-Lipschitz and `Real.smoothTransition` $T$-Lipschitz. Let `degree` be a natural number with $h_d \le \texttt{degree}$ for all $d$, and $\delta, E$ reals with $0 < \delta \le 1$ and $E > 0$.
--
--   **Statement.** There is $\rho \in \mathbb{R}_{\ge 0}$ with $0 < \rho \le 1$ and $\rho$ = `partitionedAffineSourceRadius h P A T δ E` (for these $B$, $O$, $\alpha$), and there is a real $t$ with $0 < t \le 1$ and $t$ = `partitionedAffineSourceTolerance h P A T degree δ E` (for these $G$, $Z$, $B$, $O$, $\alpha$), such that the following holds. Write $\mathcal{N}$ = `PartitionedProfileNoiseIndex G Z α B h P` and $\mathcal{X}$ = `PrincipalAxisParameter (fun d => ¬P d)` (OpenAI's index type of the joint block parameters on the axes $d$ with $\neg P(d)$). Let $z : \Omega \to (\mathcal{N} \to \mathbb{R})$ and `center, width` $: \Omega \to (\mathcal{X} \to \mathbb{R})$ have all coordinates measurable, let $\mu$ be a probability measure on $\Omega$, and assume that for $\mu$-almost every $\omega$: $|z(\omega)_j| \le 1$ for all $j$, $\delta \le |\mathrm{width}(\omega)_i|$ and $|\mathrm{center}(\omega)_i| + |\mathrm{width}(\omega)_i| \le 1$ for all $i$. Let $R : D \to \mathbb{R}$ and let $f : \Omega \times ((\Sigma_d O_d) \to \mathbb{R}) \to \mathbb{R}$ be measurable with $\|f\| \le 1$ everywhere. Put
--   - $\mathrm{slice}(\omega, x)_i = \mathrm{center}(\omega)_i + \mathrm{width}(\omega)_i\, x_i$;
--   - $\mathrm{ideal}(\omega)$ = `partitionedSlicedRegularizedIdeal h P sets ρ (center ω) (width ω) (z ω)`, a real function on $(\Sigma_d O_d) \to \mathbb{R}$ (the $\rho$-regularized density of the image of `jointBooleanSource` under the sliced partitioned ideal map);
--   - $\mathrm{post}(y)_o = R_{o.1}\, y_o$.
--
--   Then
--   $$\Bigl| \int \mathrm{ideal}(\omega)(y)\, f(\omega, \mathrm{post}(y))\ d(\mu \otimes \mathrm{Leb})(\omega, y) - \int f\bigl(\omega,\ \texttt{partitionedAllocatedProfileJet h P extra sets R t}\ (z\,\omega)\ (\mathrm{slice}(\omega, x))\bigr)\ d(\mu \otimes \beta)(\omega, x) \Bigr| \le E,$$
--   where Leb is Lebesgue measure on $(\Sigma_d O_d) \to \mathbb{R}$ and $\beta$ = `jointBooleanSource (fun d => h d)` on $\mathcal{X} \to \mathbb{R}$ (for the blocks $B_d$, $\neg P(d)$).
--
--   Lean: `OAI.Erdos3.exists_partitioned_sliced_density_comparison_with_scales_s2`, which states OpenAI's `OAI.Erdos3.exists_partitioned_sliced_density_comparison_with_scales` (in `lean/OAI/Combinatorics/Progressions/Probability/PartitionedSlicedDensityComparison.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B112`, `OAIE3v2B113` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Probability/PartitionedSlicedDensityComparison.lean (declaration OAI.Erdos3.exists_partitioned_sliced_density_comparison_with_scales)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B112
import Definitions.Def_OAIE3v2B113

section

namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

theorem exists_partitioned_sliced_density_comparison_with_scales_s2
    {Ω D G Z α : Type*} [MeasurableSpace Ω]
    [Fintype D] [Fintype G] [Fintype Z] [Fintype α] [DecidableEq α]
    {B : D → Type*} [∀ d, Fintype (B d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (P : D → Prop) [DecidablePred P]
    (extra : G → Option α → Z)
    {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)] [∀ d, Nonempty (O d)]
    (sets : ∀ d, O d → Finset α) (hsets : ∀ d, Function.Injective (sets d))
    (hcard : ∀ d o, (sets d o).card ≤ h d.val)
    (block : ∀ d, O d → B d.val) (hblock : ∀ d, Function.Injective (block d))
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    {degree : ℕ} (hdegree : ∀ d, h d ≤ degree)
    {δ E : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) (hE : 0 < E) :
    ∃ ρ : ℝ≥0, 0 < ρ ∧ ρ ≤ 1 ∧
    (ρ : ℝ) = partitionedAffineSourceRadius (B := B) (O := O) (α := α) h P A T δ E ∧
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
    t = partitionedAffineSourceTolerance (G := G) (Z := Z) (B := B) (O := O) (α := α)
      h P A T degree δ E ∧
    ∀ (z : Ω → PartitionedProfileNoiseIndex G Z α B h P → ℝ),
    (∀ j, Measurable (fun a => z a j)) →
    ∀ (center width : Ω → PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ),
    (∀ i, Measurable (fun a => center a i)) → (∀ i, Measurable (fun a => width a i)) →
    ∀ μ : Measure Ω, IsProbabilityMeasure μ →
    (∀ᵐ a ∂μ, (∀ j, |z a j| ≤ 1) ∧ (∀ i, δ ≤ |width a i|) ∧
      (∀ i, |center a i| + |width a i| ≤ 1)) →
    ∀ (R : D → ℝ) (f : Ω × ((Σ d, O d) → ℝ) → ℝ),
    Measurable f → (∀ p, ‖f p‖ ≤ 1) →
    let slice := fun a x i => center a i + width a i * x i
    let ideal := fun a => partitionedSlicedRegularizedIdeal h P sets ρ (center a) (width a) (z a)
    let post := fun (y : (Σ d, O d) → ℝ) o => R o.1.val * y o
    |(∫ p, ideal p.1 p.2 * f (p.1, post p.2) ∂μ.prod volume) -
      ∫ p, f (p.1, partitionedAllocatedProfileJet h P extra sets R t (z p.1) (slice p.1 p.2))
        ∂μ.prod (jointBooleanSource (B := fun d : {d // ¬P d} => B d.val) (α := α) (fun d => h d.val))| ≤ E := by
  sorry

end Erdos3

end

end OAI
end
