-- Prove2me | Theorems.Thm_OAI_Erdos3_residuePrimeDensity_scaled_section_norm
-- name    : OAI.Erdos3.residuePrimeDensity_scaled_section_norm
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T17:33:33.580984+00:00
-- url     : https://prove2.me/theorems/cf6a7433-0a36-42b8-85fd-25a84b0a39ab
-- title:
--   A rescaled section average of a residue prime density has ANOVA energy at most cap^2
-- statement:
--   Let $\iota$ be a finite linearly ordered type and $\sigma$ a finite type with decidable equality (section variables). Let $\mathrm{lo} : \sigma \to \mathbb{Z}$, $N : \sigma \to \mathbb{N}$, $M \in \mathbb{N}$ and $a : \sigma \to \mathbb{Z}$ be such that the residue box $\mathcal{B} = $ `IntegerResidueBox lo (lo + N) M a` — the finite set of $z : \sigma \to \mathbb{Z}$ with $\mathrm{lo}_j \le z_j < \mathrm{lo}_j + N_j$ and $z_j \equiv a_j \pmod M$ for all $j$ — is nonempty (`hne`), and let $\mathrm{moduli} : \iota \to \mathbb{N}$ take nonzero values. On $X = \prod_{i \in \iota} (\sigma \to \mathbb{Z}/\mathrm{moduli}_i)$ let $\mu$ be the product of the uniform weights `primeCoordinateReference moduli i`, and for a function $g$ on $\sigma \to \mathbb{Z}$ let $\rho_g = $ `residuePrimeCoordinateDensity lo N M a hne moduli g` be the function $y \mapsto \mathbb{E}_{z \in \mathcal{B}}[g(z)\,\mathbf{1}\{(z \bmod \mathrm{moduli}_i)_i = y\}] / \mu(y)$ on $X$ ($z$ uniform). Let $f : (\sigma \to \mathbb{Z}) \to \mathbb{R}$ with $0 \le f \le 1$ on the box `translatedIntegerBox lo N` $= \{\mathrm{lo} + y : 0 \le y_j < N_j\}$ (the section hypothesis `hf`, included in the statement).
--
--   Let $\mathrm{scale}, \mathrm{cap}, \eta$ be real numbers with $0 < \mathrm{scale}$ and $\mathrm{scale}^{-1} \le \mathrm{cap}$; let $A \subseteq \iota$ be finite and $z \in X$; let $0 \le \eta \le 1$; let $\mathcal{D}$ be a finite family of finite subsets of $\iota$, each with at most $b$ elements ($b \in \mathbb{N}$). Suppose `ProductMarginalsClose μ ρ₁ η (2b + |A|)` holds for the density $\rho_1$ of the constant function $1$ — OpenAI's predicate: for every $B \subseteq \iota$ with $|B| \le 2b + |A|$ and every $x$ with $\mu(x) \neq 0$, $|\texttt{productConditionalMean}\ \mu\ B\ \rho_1\ x - 1| \le \eta$, where `productConditionalMean μ B ρ x` $= \mathbb{E}_{y \sim \mu}\, \rho(x|_B, y|_{\iota \setminus B})$ — and suppose $2\eta\, |\mathcal{D}|^2\, 4^{b} (1 + \eta)^2 \le 1$. Let $h(y) = \mathrm{scale}^{-1} \cdot$ `productSectionAverage μ A A z ρ_f y`, where `productSectionAverage μ T A z ρ x` $= \mathbb{E}_{w \sim \mu}\, \rho\bigl(\mathrm{mix}_T(\mathrm{mix}_A(z, w), x)\bigr)$ and $\mathrm{mix}_S(u, v)$ is the point equal to $u$ on $S$ and to $v$ off $S$. Then
--   $$\sqrt{\texttt{productANOVAEnergy}\ \mu\ \mathcal{D}\ h} \le 3\,\mathrm{cap},$$
--   where `productANOVAEnergy μ D h` $= \sum_{S \in \mathcal{D}} \mathbb{E}_{\mu}\bigl[(\texttt{productANOVA}\ \mu\ S\ h)^2\bigr]$ and `productANOVA μ S h x` $= \sum_{U \subseteq S} (-1)^{|U|}\, \texttt{productConditionalMean}\ \mu\ (S \setminus U)\ h\ x$.
--
--   Lean: `OAI.Erdos3.residuePrimeDensity_scaled_section_norm` in `lean/OAI/Combinatorics/Progressions/Lattices/ResidueCellNormLengths.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B090` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/ResidueCellNormLengths.lean#L50

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

theorem residuePrimeDensity_scaled_section_norm {scale cap η : ℝ}
    (hscale : 0 < scale) (hinv : scale⁻¹ ≤ cap) (A : Finset ι) (z : ∀ i, σ → ZMod (moduli i))
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (D : Finset (Finset ι)) {b : ℕ}
    (hcard : ∀ S ∈ D, S.card ≤ b)
    (hclose : ProductMarginalsClose (primeCoordinateReference (σ := σ) moduli)
      (residuePrimeCoordinateDensity lo N M a hne moduli (fun _ => 1)) η (2 * b + A.card))
    (herr : 2 * η * (D.card : ℝ) ^ 2 * (4 : ℝ) ^ b * (1 + η) ^ 2 ≤ 1) :
    Real.sqrt (productANOVAEnergy (primeCoordinateReference (σ := σ) moduli) D
      (fun y => scale⁻¹ * productSectionAverage (primeCoordinateReference (σ := σ) moduli) A A z
        (residuePrimeCoordinateDensity lo N M a hne moduli f) y)) ≤ 3 * cap := by
  sorry

end Erdos3
end
end OAI
