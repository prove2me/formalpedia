-- Prove2me | Theorems.Thm_OAI_Erdos3_residuePrimeDensity_norm_le_three
-- name    : OAI.Erdos3.residuePrimeDensity_norm_le_three
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T17:31:16.520633+00:00
-- url     : https://prove2.me/theorems/f7b60576-8748-4326-9675-a4ec5962def3
-- title:
--   The low-degree ANOVA energy of a bounded residue prime density is at most 9
-- statement:
--   Let $\iota$ be a finite linearly ordered type and $\sigma$ a finite type with decidable equality. Let $\mathrm{lo} : \sigma \to \mathbb{Z}$, $N : \sigma \to \mathbb{N}$, $M \in \mathbb{N}$ and $a : \sigma \to \mathbb{Z}$ be such that the residue box $\mathcal{B} = $ `IntegerResidueBox lo (lo + N) M a` — the finite set of $z : \sigma \to \mathbb{Z}$ with $\mathrm{lo}_j \le z_j < \mathrm{lo}_j + N_j$ and $z_j \equiv a_j \pmod M$ for all $j$ — is nonempty (`hne`), and let $q : \iota \to \mathbb{N}$ take nonzero values. On $X = \prod_{i \in \iota} (\sigma \to \mathbb{Z}/q_i)$ let $\mu$ be the product of the uniform weights `primeCoordinateReference q i`, and for a function $g$ on $\sigma \to \mathbb{Z}$ let $\rho_g = $ `residuePrimeCoordinateDensity lo N M a hne q g` be the function $y \mapsto \mathbb{E}_{z \in \mathcal{B}}[g(z)\,\mathbf{1}\{(z \bmod q_i)_i = y\}] / \mu(y)$ on $X$ ($z$ uniform). Let $f : (\sigma \to \mathbb{Z}) \to \mathbb{R}$ with $0 \le f \le 1$ on the box `translatedIntegerBox lo N` $= \{\mathrm{lo} + y : 0 \le y_j < N_j\}$; let $\eta \in [0, 1]$; let $\mathcal{D}$ be a finite family of finite subsets of $\iota$, each with at most $b$ elements ($b \in \mathbb{N}$). Suppose `ProductMarginalsClose μ ρ₁ η (2b)` holds for the density $\rho_1$ of the constant function $1$ — OpenAI's predicate: for every $B \subseteq \iota$ with $|B| \le 2b$ and every $x$ with $\mu(x) \neq 0$, $|\texttt{productConditionalMean}\ \mu\ B\ \rho_1\ x - 1| \le \eta$, where `productConditionalMean μ B ρ x` $= \mathbb{E}_{y \sim \mu}\, \rho(x|_B, y|_{\iota \setminus B})$ — and suppose $2\eta\, |\mathcal{D}|^2\, 4^{b} (1 + \eta)^2 \le 1$. Then
--   $$\sqrt{\texttt{productANOVAEnergy}\ \mu\ \mathcal{D}\ \rho_f} \le 3,$$
--   where `productANOVAEnergy μ D ρ` $= \sum_{S \in \mathcal{D}} \mathbb{E}_{\mu}\bigl[(\texttt{productANOVA}\ \mu\ S\ \rho)^2\bigr]$ and `productANOVA μ S ρ x` $= \sum_{U \subseteq S} (-1)^{|U|}\, \texttt{productConditionalMean}\ \mu\ (S \setminus U)\ \rho\ x$.
--
--   Lean: `OAI.Erdos3.residuePrimeDensity_norm_le_three` in `lean/OAI/Combinatorics/Progressions/Lattices/ResidueCellNormLengths.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B090` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/ResidueCellNormLengths.lean#L117

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

end Erdos3

end

section

namespace Erdos3

theorem residuePrimeDensity_norm_le_three {ι σ : Type*}
    [Fintype ι] [LinearOrder ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (f : (σ → ℤ) → ℝ)
    (hf : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ f z ∧ f z ≤ 1)
    {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (D : Finset (Finset ι)) {b : ℕ}
    (hcard : ∀ S ∈ D, S.card ≤ b)
    (hclose : ProductMarginalsClose (primeCoordinateReference (σ := σ) q)
      (residuePrimeCoordinateDensity lo N M a hne q (fun _ => 1)) η (2 * b))
    (herr : 2 * η * (D.card : ℝ) ^ 2 * (4 : ℝ) ^ b * (1 + η) ^ 2 ≤ 1) :
    Real.sqrt (productANOVAEnergy (primeCoordinateReference (σ := σ) q) D
      (residuePrimeCoordinateDensity lo N M a hne q f)) ≤ 3 := by
  sorry

end Erdos3
end
end OAI
