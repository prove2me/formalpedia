-- Prove2me | Theorems.Thm_OAI_Erdos3_residuePrimeDensity_scaled_section_low_degree
-- name    : OAI.Erdos3.residuePrimeDensity_scaled_section_low_degree
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T18:10:39.209037+00:00
-- url     : https://prove2.me/theorems/a2fccb0a-2add-4a3c-a658-48ba558c3e43
-- title:
--   A rescaled section average of a residue prime density has small degree-k ANOVA energy
-- statement:
--   Let $\iota$ be a finite linearly ordered type and $\sigma$ a finite type with decidable equality (section variables). Let $\mathrm{lo} : \sigma \to \mathbb{Z}$, $N : \sigma \to \mathbb{N}$, $M \in \mathbb{N}$ and $a : \sigma \to \mathbb{Z}$ be such that the residue box $\mathcal{B} = $ `IntegerResidueBox lo (lo + N) M a` — the finite set of $z : \sigma \to \mathbb{Z}$ with $\mathrm{lo}_j \le z_j < \mathrm{lo}_j + N_j$ and $z_j \equiv a_j \pmod M$ for all $j$ — is nonempty (`hne`), and let $\mathrm{moduli} : \iota \to \mathbb{N}$ take nonzero values. On $X = \prod_{i \in \iota} (\sigma \to \mathbb{Z}/\mathrm{moduli}_i)$ let $\mu$ be the product of the uniform weights `primeCoordinateReference moduli i`, and for a function $g$ on $\sigma \to \mathbb{Z}$ let $\rho_g = $ `residuePrimeCoordinateDensity lo N M a hne moduli g` be the function $y \mapsto \mathbb{E}_{z \in \mathcal{B}}[g(z)\,\mathbf{1}\{(z \bmod \mathrm{moduli}_i)_i = y\}] / \mu(y)$ on $X$ ($z$ uniform). Let $f : (\sigma \to \mathbb{Z}) \to \mathbb{R}$ with $0 \le f \le 1$ on the box `translatedIntegerBox lo N` $= \{\mathrm{lo} + y : 0 \le y_j < N_j\}$ (the section hypothesis `hf`, included in the statement).
--
--   Let $\mathrm{scale}, \mathrm{cap}, \eta, P$ be real numbers with $0 < \mathrm{scale}$, $0 \le \mathrm{cap}$ and $\mathrm{scale}^{-1} \le \mathrm{cap}$; let $r, q, k$ be natural numbers with $2 \le q$ and $q$ even; let $A \subseteq \iota$ be finite with $|A| \le r$ and $k \le r - |A|$; let $z \in X$. Suppose $0 \le \eta$, $r \le P$, $\log(2 + \mathrm{cap}) \le P$, $P \le q \le P + 2$, and
--   $$\eta \le \tfrac12 \Bigl(\bigl(2^{r+1} (2 + |\iota|)^{r} (2 + \mathrm{cap})\bigr)^{q}\Bigr)^{-1}.$$
--   Suppose `ProductMarginalsClose μ ρ₁ η (r(q+1))` holds for the density $\rho_1$ of the constant function $1$ — OpenAI's predicate: for every $B \subseteq \iota$ with $|B| \le r(q+1)$ and every $x$ with $\mu(x) \neq 0$, $|\texttt{productConditionalMean}\ \mu\ B\ \rho_1\ x - 1| \le \eta$, where `productConditionalMean μ B ρ x` $= \mathbb{E}_{y \sim \mu}\, \rho(x|_B, y|_{\iota \setminus B})$ — and suppose `ProductBoundedMarginals μ (normalizedResiduePrimeDensity lo N M a hne moduli f scale) 1 r`: for every $B \subseteq \iota$ with $|B| \le r$ and every $x$ with $\mu(x) \neq 0$, the conditional mean over $B$ at $x$ of $\mathrm{scale}^{-1} \rho_f$ is at most $1$. Let $h(y) = \mathrm{scale}^{-1} \cdot$ `productSectionAverage μ A A z ρ_f y`, where `productSectionAverage μ T A z ρ x` $= \mathbb{E}_{w \sim \mu}\, \rho\bigl(\mathrm{mix}_T(\mathrm{mix}_A(z, w), x)\bigr)$ and $\mathrm{mix}_S(u, v)$ is the point equal to $u$ on $S$ and to $v$ off $S$. Then
--   $$\sqrt{\texttt{productANOVAEnergy}\ \mu\ \mathcal{D}_k\ h} \le \bigl(16 (P + 2)\bigr)^{2k},$$
--   where $\mathcal{D}_k$ is the family of all $k$-element subsets of $\iota$, `productANOVAEnergy μ D h` $= \sum_{S \in \mathcal{D}} \mathbb{E}_{\mu}\bigl[(\texttt{productANOVA}\ \mu\ S\ h)^2\bigr]$ and `productANOVA μ S h x` $= \sum_{U \subseteq S} (-1)^{|U|}\, \texttt{productConditionalMean}\ \mu\ (S \setminus U)\ h\ x$.
--
--   Lean: `OAI.Erdos3.residuePrimeDensity_scaled_section_low_degree` in `lean/OAI/Combinatorics/Progressions/Lattices/ResidueCellNormLengths.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B090` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/ResidueCellNormLengths.lean#L21

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι σ : Type*} [Fintype ι] [LinearOrder ι] [Fintype σ] [DecidableEq σ]
  (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
  (hne : Nonempty (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a))
  (moduli : ι → ℕ) [∀ i, NeZero (moduli i)]
  (f : (σ → ℤ) → ℝ) (hf : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ f z ∧ f z ≤ 1)

include hf

theorem residuePrimeDensity_scaled_section_low_degree {scale cap η P : ℝ}
    (hscale : 0 < scale) (hcap : 0 ≤ cap) (hinv : scale⁻¹ ≤ cap)
    {r q k : ℕ} (hq : 2 ≤ q) (heven : Even q) (A : Finset ι)
    (hAr : A.card ≤ r) (hk : k ≤ r - A.card) (z : ∀ i, σ → ZMod (moduli i))
    (hη : 0 ≤ η) (hrP : (r : ℝ) ≤ P) (hlog : Real.log (2 + cap) ≤ P)
    (hPq : P ≤ (q : ℝ)) (hqP : (q : ℝ) ≤ P + 2)
    (hsmall : η ≤ (1 / 2) * (((2 : ℝ) ^ (r + 1) * (2 + (Fintype.card ι : ℝ)) ^ r * (2 + cap)) ^ q)⁻¹)
    (hclose : ProductMarginalsClose (primeCoordinateReference (σ := σ) moduli)
      (residuePrimeCoordinateDensity lo N M a hne moduli (fun _ => 1)) η (r * (q + 1)))
    (hbound : ProductBoundedMarginals (primeCoordinateReference (σ := σ) moduli)
      (normalizedResiduePrimeDensity lo N M a hne moduli f scale) 1 r) :
    Real.sqrt (productANOVAEnergy (primeCoordinateReference (σ := σ) moduli) (Finset.univ.powersetCard k)
      (fun y => scale⁻¹ * productSectionAverage (primeCoordinateReference (σ := σ) moduli) A A z
        (residuePrimeCoordinateDensity lo N M a hne moduli f) y)) ≤ (16 * (P + 2)) ^ (2 * k) := by
  sorry

end Erdos3
end
end OAI
