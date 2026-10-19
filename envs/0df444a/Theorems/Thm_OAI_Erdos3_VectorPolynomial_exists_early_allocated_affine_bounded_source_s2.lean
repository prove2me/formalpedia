-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_early_allocated_affine_bounded_source_s2
-- name    : OAI.Erdos3.VectorPolynomial.exists_early_allocated_affine_bounded_source_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:47:19.404995+00:00
-- url     : https://prove2.me/theorems/3970795d-4ac8-4020-be3c-2b70c9898365
-- title:
--   Existence of affine source radii and a tolerance with explicit logarithmic bounds satisfying the allocated affine covered comparison
-- statement:
--   **Setting.** Let $m$ be a natural number, $G$ a finite type with decidable equality, $I : \mathrm{Fin}\ m \to \mathrm{Type}$ a family of finite types, $n : \mathrm{Fin}\ m \to \mathbb{N}$, $B$ a family of finite types with decidable equality indexed by `LayerSamplerAxis I n` $= \Sigma_{j}\, (I\ j \oplus \mathrm{Fin}\ (n\ j))$, $\alpha$ a finite type with decidable equality, and $O : \mathrm{Fin}\ m \to \mathrm{Type}$ a family of finite nonempty types with decidable equality. Let $\mathrm{rows}_j : O_j \to \mathrm{Finset}\ \alpha$ be injective with $|\mathrm{rows}_j(a)| \le j + 1$ for all $j, a$.
--
--   **Hypotheses.** Let $\psi : \mathbb{R} \to \mathbb{R}$ be $C^\infty$ with values in $[0, 1]$, $\psi(t) = 0$ for $|t| \le 1$ and $\psi(t) = 1$ for $|t| \ge 2$. Let $A, T \in \mathbb{R}_{\ge 0}$ with $\psi$ $A$-Lipschitz and `Real.smoothTransition` $T$-Lipschitz. For every axis $a$ let $\mathrm{block}_a : O_{a_1} \to B\ a$ be injective, where $a_1$ is the layer index of $a$. Let $\delta, \mathrm{target}, \mathrm{maskLog}, F, D$ be real numbers such that `AllocatedComparisonDimensions B α O D` holds (a structure defined by OpenAI: $D \ge 0$, and $m$, $|G|$, $|\alpha|$, the number of axes, the number of principal tuple indices and parameters, the number of outputs, each $|O_j|$ and each number of bounded coefficient exponents are at most $D$), $0 < \delta \le 1$, $\mathrm{target} \ge 0$, $\mathrm{maskLog} \ge 0$, $F \ge 0$, and $(\delta/2)^{-1} \le e^{F}$.
--
--   **Conclusion.** Put $E = \mathrm{target} + \mathrm{maskLog} + 5$, $\eta = e^{-E}$, $\mathrm{radiusLog} = 2\cdot$`affineProfileInputEnvelope D A T E F` $+ 2$, and $\mathrm{toleranceLog}$ = `affineProfileToleranceEnvelope m D (D(D+1) + D·D + D + 1) A T E F` (explicit envelopes defined by OpenAI). Then there exists $\rho$ assigning to each predicate $P$ on `LayerSamplerAxis I n` a number $\rho(P) \in \mathbb{R}_{\ge 0}$ such that
--
--   - for every $P$: $0 < \rho(P) \le 1$ and $e^{-\mathrm{radiusLog}} \le \rho(P)$;
--   - for every $P$: $\rho(P)$ = `partitionedAffineSourceRadius (layerSamplerDegree I n) P A T (δ/2) η` (an explicit radius defined by OpenAI, taken with the axis family $B$, the output types $O_{a_1}$ for the axes $a$ not satisfying $P$, and $\alpha$);
--
--   and there exists a real $t$ with $0 < t \le 1$ such that $t^{-1} \le e^{\mathrm{toleranceLog}}$, $t$ = `allocatedAffineSourceTolerance B A T (δ/2) η` (the minimum over all predicates $P$ of explicit tolerances, defined by OpenAI), and `AllocatedAffineCoveredComparison B rows δ η ρ t` holds. The latter is a predicate defined by OpenAI (instantiated here at fixed universe levels) asserting an estimate, uniform over all ambient data $J, U, \mathrm{basis}, R, \sigma, S$ with $\sigma_j \le t$, all $x$, $u$, kernel selections $s$ with nonsingular jets, inverse bounds, progression and residue data, logarithmic size parameters and bounded measurable test functions $F$, for the difference between the actual covered physical test mean (an integral of $F$ over the coefficient source and the deck residues) and a model expression built from the averaged sliced profile ideal with radius $\rho(\texttt{allocatedGridAxis U basis S.value})$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_early_allocated_affine_bounded_source_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.exists_early_allocated_affine_bounded_source` (in `lean/OAI/Combinatorics/Progressions/Lattices/AllocatedAffineWholeProfileComparison.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B213` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AllocatedAffineWholeProfileComparison.lean (declaration OAI.Erdos3.VectorPolynomial.exists_early_allocated_affine_bounded_source)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B213

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
universe uJ uQ
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j a, (rows j a).card ≤ j.val + 1)

include hrows hcard in
theorem exists_early_allocated_affine_bounded_source_s2
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (block : ∀ a : LayerSamplerAxis I n, O a.1 → B a)
    (hblock : ∀ a, Function.Injective (block a))
    {δ target maskLog F D : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B α O D) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (htarget : 0 ≤ target) (hmaskLog : 0 ≤ maskLog) (hF : 0 ≤ F)
    (hδF : (δ / 2)⁻¹ ≤ Real.exp F) :
    let E := target + maskLog + 5
    let η := Real.exp (-E)
    let radiusLog := 2 * affineProfileInputEnvelope D (A : ℝ) (T : ℝ) E F + 2
    let toleranceLog := affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1) (A : ℝ) (T : ℝ) E F
    ∃ ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0,
      (∀ P, 0 < ρ P ∧ ρ P ≤ 1 ∧ Real.exp (-radiusLog) ≤ ρ P) ∧
      (∀ P, (ρ P : ℝ) = partitionedAffineSourceRadius (B := B)
        (O := fun a : {a // ¬P a} => O a.val.1) (α := α)
        (layerSamplerDegree I n) P A T (δ / 2) η) ∧
      ∃ t : ℝ, 0 < t ∧ ∃ htone : t ≤ 1,
        t⁻¹ ≤ Real.exp toleranceLog ∧
        t = allocatedAffineSourceTolerance (G := G) (O := O) (α := α) B A T (δ / 2) η ∧
        AllocatedAffineCoveredComparison.{uJ,uQ,_,_,_,_,_} (G := G) B rows δ η ρ t htone := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
