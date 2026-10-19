-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedAffineProductMixed_primePower_event_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedAffineProductMixed_primePower_event_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:55:11.988231+00:00
-- url     : https://prove2.me/theorems/191537fb-153c-425c-a2bc-d78b38466d9a
-- title:
--   The modulus-bad event at every prime power of a deep prime set has small probability under the affine product mixed law
-- statement:
--   Let $m$ and $L$ be natural numbers, $G$ and $X$ finite types, and for each $j < m$ let $I_j$ and $E_j$ be finite types and $n_j$ a natural number; for each layer sampler axis $a$ (an element of OpenAI's `LayerSamplerAxis I n`) let $B_a$ be a finite type. We use OpenAI's index types: `LayerSamplerVariables G I n B` (the layer sampler variables), `AllocatedFullSmoothCoefficientIndex G X I n B` $= (\mathrm{Option}(\text{variables}) \times X) \sqcup (\text{bounded-degree coefficient slots})$ (the smooth coefficients), `AllocatedFullContinuousCoefficientIndex G I n B` (the continuous coefficients), `CoefficientDeckScalarIndex (variables) E` (the deck coefficients: triples of $j < m$, an exponent of total degree at most $j+1$ in the variables, and an element of $E_j$), and `AllocatedSmoothRankCoefficientIndex X inactive L` (the selected smooth coefficients).
--
--   Let `inactive` be a predicate on layer sampler axes; let `spatial` be an embedding $\{0,\dots,L-1\} \hookrightarrow G$, `kernel j` an embedding $\{0,\dots,L-1\} \times \{0, \dots, j\} \hookrightarrow G$ for each $j < m$, and `block j b` an embedding $\{0,\dots,L-1\} \hookrightarrow B_{(j,b)}$ for each $j$ and each degree-active axis $b$ (OpenAI's `AllocatedDegreeActiveAxis inactive j`). Let $\mathrm{continuous}$ be an integer assignment to the continuous coefficients, $\mathrm{stride} : X \to \mathbb{N}$ with $\mathrm{stride}(x) > 0$ for all $x$, $\mathrm{residue} : \mathrm{Option}(\text{variables}) \times X \to \mathbb{Z}$, and $\mathrm{laws}$ a probability mass function on $\mathbb{Z}$ for each smooth coefficient. Let $N$ be a nonzero natural number and $D$ a natural number, and assume $0 < m$. Let $\mathrm{center}, \mathrm{width}$ be real functions on the selected smooth coefficients with $\mathrm{width}_i > 0$ for every $i$ and `shiftedSmoothProductMass center width` $> 0$ (OpenAI: $\sum_{k} \prod_i \phi\bigl((k_i - \mathrm{center}_i)/\mathrm{width}_i\bigr)$ over integer vectors $k$, with $\phi$ OpenAI's smooth probability profile). Assume that for every selected smooth coefficient $i$, the law at its image under the embedding `allocatedSmoothFullEmbedding inactive spatial block` (OpenAI) is `shiftedSmoothCoefficientPMF (center i) (width i)`, the probability mass function on $\mathbb{Z}$ proportional to $k \mapsto \phi((k - \mathrm{center}_i)/\mathrm{width}_i)$.
--
--   Let $\mathcal{P}$ be a finite set of natural numbers and $A : \mathbb{N} \to \mathbb{N}$, and assume: every $p \in \mathcal{P}$ is prime; $p^{A(p)} \mid N$, $0 < A(p)$, and $2\,v_p(\mathrm{stride}(x)) \le A(p)$ for every $x \in X$ (where $v_p$ is the exponent of $p$ in the factorization), for every $p \in \mathcal{P}$; $|X| + \sum_{j < m} (|E_j| + n_j) \le D$. Let $C \ge 0$ be real, and assume
--   $$\Bigl\lceil \frac{2(C + D + 10)}{\texttt{modularRankSmallBallExponent}\ m} \Bigr\rceil \le L,$$
--   where `modularRankSmallBallExponent m` $= 2^{1-m}$; `modularCoefficientPrimeThreshold m` $\le p^{A(p)}$ for every $p \in \mathcal{P}$, where `modularCoefficientPrimeThreshold m` $= \max\bigl(2, \lceil m^{4/2^{1-m}} \rceil\bigr)$; and, writing $Q = \prod_{p \in \mathcal{P}} p^{A(p)}$ and $\Lambda$ = `probabilityProfileLipschitz` (a Lipschitz constant of $\phi$, chosen by OpenAI), $8\Lambda Q \le \mathrm{width}_i$ for every $i$. (All ceilings are natural-number ceilings.)
--
--   Sample the smooth coefficients $x$ independently with the given laws (OpenAI's `independentProductPMF laws`), and then, independently, a uniformly random assignment $\mathrm{deck}$ of elements of $\mathbb{Z}/N\mathbb{Z}$ to the deck coefficients. Form the integer coefficient array `allocatedMixedFullArray (allocatedFullSmoothAffine stride residue x) deck' continuous`, where the smooth part is the affine image of $x$ (the coefficient at $t = (v, x')$ in the first summand becomes $\mathrm{residue}(t) + \mathrm{stride}(x')\,x(t)$, the others are unchanged), the deck part $\mathrm{deck}'$ consists of the canonical representatives in $\{0, \dots, N-1\}$ of the deck values, and the continuous part is $\mathrm{continuous}$. Then the probability that, for every $p \in \mathcal{P}$, the array satisfies `allocatedActualModulusBad inactive spatial kernel block C (p^{A(p)})` is at most
--   $$\frac{1}{Q^{10}} + \sum_{i} \frac{16\,\Lambda\,Q}{\mathrm{width}_i},$$
--   the sum running over the selected smooth coefficients $i$. Here `allocatedActualModulusBad … C M f` is a proposition defined by OpenAI: reading noise, deck and projection data off the array $f$ and reducing the selected coefficients modulo $M$, there are a variable assignment $v$ modulo $M$, an index $j$ and a vector $w$ modulo $M$ with at least one unit entry such that a certain rank failure probability exceeds $M^{-C}$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedAffineProductMixed_primePower_event_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedAffineProductMixed_primePower_event` (in `lean/OAI/Combinatorics/Progressions/Lattices/AllocatedModularRankAffineFullWitness.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B236` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AllocatedModularRankAffineFullWitness.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedAffineProductMixed_primePower_event)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B236

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical
open FiniteProbabilityWeights
attribute [local irreducible] allocatedActualModulusBad allocatedMixedFullArray independentProductPMF

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

attribute [local instance] OAI.Erdos3.VectorPolynomial.affineFullWitnessSmoothFintype
noncomputable local instance affineFullWitnessSmoothDecidableEq_rfb5931_1 :
    DecidableEq (AllocatedFullSmoothCoefficientIndex G X I n B) := Classical.decEq _
noncomputable local instance affineFullWitnessSelectedSmoothDecidableEq_rfb5931_1 (inactive : LayerSamplerAxis I n → Prop) :
    DecidableEq (AllocatedSmoothRankCoefficientIndex X inactive L) := Classical.decEq _
attribute [local instance] OAI.Erdos3.VectorPolynomial.affineFullWitnessDeckFintype
attribute [local instance] OAI.Erdos3.VectorPolynomial.affineFullWitnessDeckDecidableEq
noncomputable local instance affineFullWitnessSelectedSmoothFintype_rfb5931_1 (inactive : LayerSamplerAxis I n → Prop) :
    Fintype (AllocatedSmoothRankCoefficientIndex X inactive L) := inferInstance
attribute [local instance] OAI.Erdos3.VectorPolynomial.affineFullWitnessSelectedDeckFintype
attribute [local instance] OAI.Erdos3.VectorPolynomial.affineFullWitnessSelectedDeckDecidableEq
theorem allocatedAffineProductMixed_primePower_event_s2
    (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (continuous : AllocatedFullContinuousCoefficientIndex G I n B → ℤ)
    (stride : X → ℕ) (hstride : ∀ x, 0 < stride x)
    (residue : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (laws : AllocatedFullSmoothCoefficientIndex G X I n B → PMF ℤ)
    {N D : ℕ} [NeZero N] (hm : 0 < m)
    (center width : AllocatedSmoothRankCoefficientIndex X inactive L → ℝ)
    (hwidth : ∀ j, 0 < width j) (hZ : 0 < shiftedSmoothProductMass center width)
    (hcoordinate : ∀ i, laws (allocatedSmoothFullEmbedding inactive spatial block i) =
      shiftedSmoothCoefficientPMF (center i) (width i) (hwidth i)
        (shiftedSmoothProductMass_coordinate_pos center width hwidth hZ i))
    (P : Finset ℕ) (A : ℕ → ℕ) [∀ p : P, NeZero p.val]
    (hprime : ∀ p ∈ P, p.Prime) (hcover : ∀ p ∈ P, p ^ A p ∣ N)
    (hpositive : ∀ p ∈ P, 0 < A p)
    (hdeep : ∀ p ∈ P, ∀ x, 2 * (stride x).factorization p ≤ A p)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) ≤ D)
    {C : ℝ} (hC : 0 ≤ C)
    (hL : ⌈2 * (C + D + 10) / modularRankSmallBallExponent m⌉₊ ≤ L)
    (hthreshold : ∀ p ∈ P, modularCoefficientPrimeThreshold m ≤ p ^ A p)
    (hlarge : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) *
      (∏ p : P, p.val ^ A p.val) ≤ width j) :
    (((independentProductPMF laws).bind
      (fun x => (PMF.uniformOfFintype
        (CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E → ZMod N)).map
        (fun deck => decide (∀ p : P,
          allocatedActualModulusBad inactive spatial kernel block C (p.val ^ A p.val)
            (allocatedMixedFullArray (allocatedFullSmoothAffine (fun x => (stride x : ℤ)) residue x)
            (fun i => (deck i).val) continuous))))) true).toReal ≤
      1 / ((∏ p : P, p.val ^ A p.val : ℕ) : ℝ) ^ 10 +
        ∑ j, 16 * (probabilityProfileLipschitz : ℝ) * (∏ p : P, p.val ^ A p.val) / width j := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
