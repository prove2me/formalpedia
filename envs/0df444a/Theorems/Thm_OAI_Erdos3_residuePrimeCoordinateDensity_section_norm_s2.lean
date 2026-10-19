-- Prove2me | Theorems.Thm_OAI_Erdos3_residuePrimeCoordinateDensity_section_norm_s2
-- name    : OAI.Erdos3.residuePrimeCoordinateDensity_section_norm_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:35:57.803699+00:00
-- url     : https://prove2.me/theorems/fb266386-88e5-416c-b0a4-709e76c9a041
-- title:
--   The low-degree ANOVA norm of the K-section of a residue prime-coordinate density equals a mass ratio times the norm of the outside density on a cell
-- statement:
--   Let $\iota, \sigma$ be finite types with decidable equality. Let $\ell : \sigma \to \mathbb{Z}$, $N : \sigma \to \mathbb{N}$, $M \in \mathbb{N}$ and $a : \sigma \to \mathbb{Z}$, and let $\mathcal{B}$ = `IntegerResidueBox` be the set of $z \in \mathbb{Z}^\sigma$ with $\ell_k \le z_k < \ell_k + N_k$ and $z_k \equiv a_k \pmod M$ for all $k$; assume $\mathcal{B}$ is nonempty. Let $q : \iota \to \mathbb{N}$ with all $q_i \ne 0$ and pairwise coprime. Let $K \subseteq \iota$ be a finite set, $\mathrm{base}_i \in (\mathbb{Z}/q_i)^\sigma$ for $i \in \iota$, and $u$ an element of `ResiduePrimeCoordinateCell ℓ N M a q K base`, i.e. a point of $\mathcal{B}$ whose reduction modulo $q_i$ is $\mathrm{base}_i$ for every $i \in K$. Let $f : \mathbb{Z}^\sigma \to \mathbb{R}$ and $B \in \mathbb{N}$.
--
--   Let $\mu$ be the family of uniform laws on $(\mathbb{Z}/q_i)^\sigma$ (`primeCoordinateReference`), and $\mu'$ the same family restricted to $\iota' = \{i \notin K\}$. Let $\rho$ = `residuePrimeCoordinateDensity ℓ N M a _ q f`: the density with respect to $\prod_i \mu_i$ of the reduction modulo $q$ of a uniform point $x \in \mathcal{B}$, weighted by $f(x)$ (defined by OpenAI). Let $\bar\rho$ = `productSectionAverage μ K K base ρ`, the function $x \mapsto \mathbb{E}_{y}\, \rho(\text{point equal to } \mathrm{base} \text{ on } K \text{ and } x \text{ off } K)$ (by definition this is $\mathbb{E}_{y \sim \prod_i \mu_i}\, \rho(\mathrm{mix}_K(\mathrm{mix}_K(\mathrm{base}, y), x))$, where $\mathrm{mix}_K(v, w)$ equals $v$ on $K$ and $w$ off $K$). Let $\rho_{\mathrm{out}}$ = `residueCellOutsideDensity ℓ N M a q K base u f`: the density with respect to $\prod_{i \in \iota'} \mu_i$ of the reductions modulo $q_i$, $i \notin K$, of a uniform point $x$ of the cell (the points of $\mathcal{B}$ reducing to $\mathrm{base}$ on $K$), weighted by $f(x)$. Then
--   $$\sqrt{\texttt{productANOVAEnergy}\ \mu\ \mathcal{D}_B(\iota)\ \bar\rho} = \texttt{residuePrimeCoordinateMassRatio ℓ N M a q K base} \cdot \sqrt{\texttt{productANOVAEnergy}\ \mu'\ \mathcal{D}_B(\iota')\ \rho_{\mathrm{out}}},$$
--   where $\mathcal{D}_B(\cdot)$ = `lowDegreeCoordinateSets · B` is the family of subsets of size at most $B$, `productANOVAEnergy μ 𝒟 g` is the sum over $S \in \mathcal{D}$ of the mean square of the ANOVA component of $g$ for $S$ (defined by OpenAI), and `residuePrimeCoordinateMassRatio ℓ N M a q K base` (defined by OpenAI) is the proportion $|\text{cell}| / |\mathcal{B}|$ of points of $\mathcal{B}$ in the cell, divided by the $\prod_i \mu_i$-mass of the set of residue patterns that agree with $\mathrm{base}$ on $K$.
--
--   Lean: `OAI.Erdos3.residuePrimeCoordinateDensity_section_norm_s2`, which states OpenAI's `OAI.Erdos3.residuePrimeCoordinateDensity_section_norm` (in `lean/OAI/Combinatorics/Progressions/Lattices/AffineMaskedInitialShell.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B193`, `OAIE3v2B197` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AffineMaskedInitialShell.lean (declaration OAI.Erdos3.residuePrimeCoordinateDensity_section_norm)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B193
import Definitions.Def_OAIE3v2B197

section

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem residuePrimeCoordinateDensity_section_norm_s2 {ι σ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (hpair : Pairwise (fun i k => (q i).Coprime (q k)))
    (K : Finset ι) (base : ∀ i, σ → ZMod (q i))
    (u : ResiduePrimeCoordinateCell lo N M a q K base) (f : (σ → ℤ) → ℝ) (B : ℕ) :
    Real.sqrt (productANOVAEnergy (primeCoordinateReference (σ := σ) q) (lowDegreeCoordinateSets ι B)
      (productSectionAverage (primeCoordinateReference (σ := σ) q) K K base
        (residuePrimeCoordinateDensity lo N M a hne q f))) =
      residuePrimeCoordinateMassRatio lo N M a q K base *
        Real.sqrt (productANOVAEnergy (primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val))
          (lowDegreeCoordinateSets {i // i ∉ K} B) (residueCellOutsideDensity lo N M a q K base u f)) := by
  sorry

end Erdos3

end

end OAI
end
