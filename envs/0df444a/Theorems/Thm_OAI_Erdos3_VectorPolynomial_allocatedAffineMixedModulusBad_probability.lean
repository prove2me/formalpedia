-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedAffineMixedModulusBad_probability
-- name    : OAI.Erdos3.VectorPolynomial.allocatedAffineMixedModulusBad_probability
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T01:11:23.327975+00:00
-- url     : https://prove2.me/theorems/557d1ef1-d34c-4722-9b32-5c27ca95bdd1
-- title:
--   A uniform mixed coefficient vector mod p^a is modulus-bad with probability at most p^(-10a)
-- statement:
--   Let $m,L\in\mathbb N$, $G,X$ finite types, $I,E\colon\mathrm{Fin}\,m\to$ Type families of finite types, $n\colon\mathrm{Fin}\,m\to\mathbb N$, and $B$ a family of finite types indexed by `LayerSamplerAxis I n` $=\Sigma_j\,I_j\oplus\mathrm{Fin}\,n_j$. Let `inactive` be a predicate on `LayerSamplerAxis I n`; `noise` $\colon\mathrm{Option}($`LayerSamplerVariables G I n B`$)\times X\to\mathbb Z$; $r_j\colon$ `BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j + 1)` $\to E_j\to\mathbb Z$ for each $j$; `projection` $j\colon$ `AllocatedDegreeActiveAxis inactive j` $\to$ `BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j + 1)` $\to\mathbb Z$ (where `AllocatedDegreeActiveAxis inactive j` is the set of $a\in I_j\oplus\mathrm{Fin}\,n_j$ with $\langle j,a\rangle$ not inactive); and embeddings `spatial` $\colon\mathrm{Fin}\,L\hookrightarrow G$, `kernel` $j\colon\mathrm{Fin}\,L\times\mathrm{Fin}(j+1)\hookrightarrow G$, `block` $j\ b\colon\mathrm{Fin}\,L\hookrightarrow B\langle j,b\rangle$. Let $p,a,D$ be natural numbers with $p$ prime, $a>0$, $m>0$, and $|X|+\sum_j(|E_j|+n_j)\le D$. Let `stride` $\colon X\to\mathbb N$ be positive with $2\,v_p(\mathrm{stride}(x))\le a$ for all $x$ ($v_p$ the exponent of $p$, `Nat.factorization`), `offset` an integer for each element of `AllocatedCongruenceCoefficientIndex X E inactive L`, and $C\ge0$ real, with `modularCoefficientPrimeThreshold m` $\le p^a$ (this threshold is $\max(2,\lceil m^{4/\kappa}\rceil)$ with $\kappa=$ `modularRankSmallBallExponent m` $=2^{1-m}$) and $\lceil 2(C+D+10)/\kappa\rceil\le L$. Then under the uniform distribution on functions from `AllocatedSmoothRankCoefficientIndex X inactive L` $\oplus$ `AllocatedDeckRankCoefficientIndex E L` to $\mathbb Z/p^a$, the event `allocatedAffineMixedModulusBad inactive noise r projection spatial kernel block stride offset C (p ^ a)` has probability at most $1/(p^a)^{10}$. Here `allocatedAffineMixedModulusBad … C M x` is the predicate `allocatedCongruenceModulusBad … C M` applied to the coefficients `allocatedCongruenceAffineCoefficients` built from the strides and offsets mod $M$ and from $x$ (via `allocatedMixedCoefficientEquiv`); `allocatedCongruenceModulusBad … C N x` says that there exist $v$, $j$ and $w$ with some coordinate of $w$ a unit mod $N$ such that $N^{-C}$ is less than `allocatedCongruenceRankFailureProbability` of the data reduced mod $N$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedAffineMixedModulusBad_probability` in `lean/OAI/Combinatorics/Progressions/Lattices/AllocatedModularRankAffineFullWitness.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B130`, `OAIErdos3B147` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AllocatedModularRankAffineFullWitness.lean#L332

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B130
import Definitions.Def_OAIErdos3B147

namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]
variable (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (C : ℝ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical
open FiniteProbabilityWeights

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

variable (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)

theorem allocatedAffineMixedModulusBad_probability {p a D : ℕ} [NeZero p]
    (hm : 0 < m) (hp : p.Prime) (ha : 0 < a)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) ≤ D)
    (stride : X → ℕ) (hstride : ∀ x, 0 < stride x)
    (hdeep : ∀ x, 2 * (stride x).factorization p ≤ a)
    (offset : AllocatedCongruenceCoefficientIndex X E inactive L → ℤ)
    {C : ℝ} (hC : 0 ≤ C)
    (hlarge : modularCoefficientPrimeThreshold m ≤ p ^ a)
    (hL : ⌈2 * (C + D + 10) / modularRankSmallBallExponent m⌉₊ ≤ L) :
    (uniform ((AllocatedSmoothRankCoefficientIndex X inactive L ⊕
      AllocatedDeckRankCoefficientIndex E L) → ZMod (p ^ a))).eventProbability
        (allocatedAffineMixedModulusBad inactive noise r projection spatial kernel block
          stride offset C (p ^ a)) ≤ 1 / ((p ^ a : ℕ) : ℝ) ^ 10 := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
