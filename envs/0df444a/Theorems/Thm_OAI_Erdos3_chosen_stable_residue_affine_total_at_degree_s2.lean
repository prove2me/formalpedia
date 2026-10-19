-- Prove2me | Theorems.Thm_OAI_Erdos3_chosen_stable_residue_affine_total_at_degree_s2
-- name    : OAI.Erdos3.chosen_stable_residue_affine_total_at_degree_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:31:27.750796+00:00
-- url     : https://prove2.me/theorems/4fe1e90c-ff4f-48a7-a70a-89c44dcc8ea2
-- title:
--   On a stable residue cell, the truncated affine residue pairing of the removal-chain density with h minus (1+ε)·level·g is small
-- statement:
--   **Data.** Let $\Omega, \iota, \sigma, J$ be finite types, with $\iota$ linearly ordered. Let $h, g : \mathbb{Z}^\sigma \to \mathbb{C}$, $\ell, a : \sigma \to \mathbb{Z}$, $N : \sigma \to \mathbb{N}$, $M \in \mathbb{N}$, and $q : \iota \to \mathbb{N}$ with all $q_i \ne 0$. Let $\varepsilon, L, T, C, \mathrm{shell}, \mathrm{modLog}, \mathrm{level}$ be reals, $K \subseteq \iota$ a finite set, $\mathrm{base}_i \in (\mathbb{Z}/q_i)^\sigma$ for $i \in \iota$, and $b \in \mathbb{N}$. Write $\iota' = \{i \in \iota : i \notin K\}$, and use the following explicit quantities defined by OpenAI: $j_0$ = `affineRemovalDepth T` and $r_0$ = `affineComparisonTail ε L T` (natural numbers given by the iteration counts `CyclicCrootSisask.spectralIterations 1 T` and `spectralIterations (ε/(2+ε)) (L + 2T + 4)`), $P_0$ = `affineComparisonScale ε L T C` $= L + T + 2 + (j_0 + r_0) + C$, $\mathrm{mom}$ = `affineComparisonMoment P₀` $= 2(\lfloor P_0/2 \rfloor + 1)$, and $d_0 = \max\bigl((j_0 + r_0)(\mathrm{mom} + 1),\ 2b + j_0\bigr)$. Let $\mu$ be the family of uniform laws on $(\mathbb{Z}/q_i)^{\mathrm{Option}\,J \times \sigma}$, $i \in \iota'$ (`primeCoordinateReference`). Let $p$ be a finite probability law on $\Omega$, $F : \Omega \to \prod_{i \in \iota'} (\mathbb{Z}/q_i)^{\mathrm{Option}\,J \times \sigma}$, $\mathrm{sourceBase} \in \prod_{i \in \iota'} (\mathbb{Z}/q_i)^{\mathrm{Option}\,J \times \sigma}$, $\mathrm{siteBase} \in \prod_{i \in \iota'} (\mathbb{Z}/q_i)^{\sigma}$, functions $w, \mathrm{rem} : \Omega \to \mathbb{R}$, and a list $cs$ of product cylinders. Let $\mathrm{prime}, \mathrm{power} : \iota \to \mathbb{N}$, $\mathrm{dimLog} \in \mathbb{R}$, and let $u$ be an element of `ResiduePrimeCoordinateCell ℓ N M a q K base`, i.e. a point $z$ of the residue box $\{z \in \mathbb{Z}^\sigma : \ell_k \le z_k < \ell_k + N_k,\ z_k \equiv a_k \pmod M\}$ whose reduction modulo $q_i$ equals $\mathrm{base}_i$ for every $i \in K$.
--
--   **Hypotheses.**
--   - $\texttt{affineComparisonDegree}\ |\mathrm{Option}\,J \times \sigma|\ |\sigma|\ \varepsilon\ L\ T\ C\ \mathrm{shell}\ \mathrm{modLog} \le b$, where `affineComparisonDegree` is an explicit natural number defined by OpenAI;
--   - `CylinderRemovalChain μ sourceBase p F 2 (exp(-T)) j₀ r₀ w rem cs` (an inductive predicate defined by OpenAI: $\mathrm{rem}$ is obtained from $w$ by successively removing the cylinders in $cs$, each on at most $j_0$ coordinates, of mass greater than $e^{-T}$ for the current observed density, and with marginals of the normalized section bounded by $2$ up to order $r_0$);
--   - $0 \le w \le 1$ and $0 \le \mathrm{rem} \le 1$ on $\Omega$, and $\mathbb{E}_p[\mathrm{rem}] \le e^{-T}$;
--   - `ResiduePrimeCoordinateStable g ℓ N M a q (j₀ + r₀) (affineStabilityTolerance T) K base` (defined by OpenAI: for every set $J'$ of at most $j_0 + r_0$ indices disjoint from $K$ and every residue pattern $y$ agreeing with $\mathrm{base}$ on $K$ whose cell on $K \cup J'$ is nonempty, the mean of $g$ over the cell of $\mathrm{base}$ on $K$ and the mean over the cell of $y$ on $K \cup J'$ differ by at most $e^{-(T+4)}$);
--   - `PrimeRefinementUpperBound h g ℓ N M a q (j₀ + r₀) level (affineIncrementTolerance L T) (affineStabilityTolerance T) K base` (defined by OpenAI: for every such $J'$ and $y$, the real part of the mean of $h$ over the cell of $y$ on $K \cup J'$ is at most $\mathrm{level}$ times the real part of the mean of $g$ over the cell of $\mathrm{base}$ on $K$, plus $e^{-(L+T+4)} + \mathrm{level} \cdot e^{-(T+4)}$);
--   - $0 < M$; the $q_i$ are pairwise coprime; $M$ is coprime to $q_i$ for every $i \notin K$;
--   - $0 \le \operatorname{Re} g(z) \le 1$ and $0 \le \operatorname{Re} h(z) \le 1$ for all $z$ in the box $\prod_k [\ell_k, \ell_k + N_k)$;
--   - $0 \le L$, $0 \le T$, $e^{-L} \le \mathrm{level}$, $\mathrm{level} \le 2$;
--   - `ProductMarginalsClose μ (observedProductDensity μ p F 1) (affineComparisonAccuracy b P₀ L T) d₀`: for every set of at most $d_0$ indices of $\iota'$, the conditional means of the density of the law of $F$ under $p$ (relative to $\mu$) are within $\exp(-A)$ of $1$, where $A$ = `affineComparisonAccuracyLog b P₀ L T` $= (P_0 + 3)^3 + 2b(P_0 + 2) + L + T + 4$;
--   - $q_i = \mathrm{prime}_i^{\mathrm{power}_i}$ with $\mathrm{prime}_i$ prime, for all $i \in \iota$;
--   - $2 \le |J|$; $0 < \mathrm{shell}$; $0 \le \mathrm{modLog}$; $q_i \le e^{\mathrm{modLog}}$ for $i \notin K$; $0 < \varepsilon$; $0 \le C$; $|\iota| \le e^{C}$;
--   - `affineMandatoryPrimes prime (ε/(2+ε)) P₀` $\subseteq K$ (the indices $i$ with $\mathrm{prime}_i$ at most an explicit threshold `affineComparisonPrimeThreshold (ε/(2+ε)) P₀` defined by OpenAI);
--   - $|\sigma| \le e^{\mathrm{dimLog}}$;
--   - for every $k \in \sigma$, $\exp\bigl(\mathrm{modLog} \cdot d_0 + A + \mathrm{dimLog} + 1\bigr) \le$ `residueIndexLength (ℓ k) (ℓ k + N k) (lcm(M, ∏_{i∈K} q_i)) (u_k)`, the number of integers in $[\ell_k, \ell_k + N_k)$ congruent to $u_k$ modulo $\operatorname{lcm}(M, \prod_{i \in K} q_i)$.
--
--   **Conclusion.** Let $\rho[f]$ denote `residuePrimeCoordinateDensity ℓ N (lcm(M, ∏_{i∈K} q_i)) u (_) q' f` with $q' = q|_{\iota'}$: the density on $\prod_{i \in \iota'} (\mathbb{Z}/q_i)^\sigma$, relative to the uniform law, of the reductions of a uniform point $x$ of the residue box $\{x : \ell_k \le x_k < \ell_k + N_k,\ x_k \equiv u_k \pmod{\operatorname{lcm}(M, \prod_{i \in K} q_i)}\}$, weighted by $f(x)$ (defined by OpenAI). Then
--   $$\texttt{affineResidueTruncatedPairing}\ q'\ \mathcal{D}_b\ \bigl(\texttt{observedProductDensity}\ \mu\ p\ F\ w\bigr)\ \bigl(\rho[\operatorname{Re} h] - (1 + \varepsilon)\,\mathrm{level}\,\rho[\operatorname{Re} g]\bigr)$$
--   $$\le \mathrm{level}\,(1 + 2\varepsilon)\, e^{-T} + \frac{\mathrm{shell}}{16} + \sqrt{3 e^{-T}}\,\bigl(3 + 3(1 + \varepsilon)\,\mathrm{level}\bigr),$$
--   where $\mathcal{D}_b$ = `lowDegreeCoordinateSets ι' b` is the family of subsets of $\iota'$ of size at most $b$, `observedProductDensity μ p F w` is the density relative to $\mu$ of the $w$-weighted law of $F$ under $p$, and `affineResidueTruncatedPairing` (defined by OpenAI) is the pairing, under the affine sample coupling of $(\mathbb{Z}/q_i)^{\mathrm{Option}\,J \times \sigma}$ with $(\mathbb{Z}/q_i)^{\sigma}$, of the ANOVA truncations to $\mathcal{D}_b$ of the two functions.
--
--   (The datum $\mathrm{siteBase}$ is an argument of the theorem but does not appear in any hypothesis or in the conclusion.)
--
--   Lean: `OAI.Erdos3.chosen_stable_residue_affine_total_at_degree_s2`, which states OpenAI's `OAI.Erdos3.chosen_stable_residue_affine_total_at_degree` (in `lean/OAI/Combinatorics/Progressions/Polynomial/InitialMaskedAffineComparisonAtDegree.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B193`, `OAIE3v2B197` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Polynomial/InitialMaskedAffineComparisonAtDegree.lean (declaration OAI.Erdos3.chosen_stable_residue_affine_total_at_degree)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B193
import Definitions.Def_OAIE3v2B197

section

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

section

variable {Ω ι σ J : Type*} [Fintype J] [Fintype Ω] [Fintype ι] [LinearOrder ι] [Fintype σ]
variable {h g : (σ → ℤ) → ℂ} {lo a : σ → ℤ} {N : σ → ℕ} {M : ℕ} {q : ι → ℕ}
variable [∀ i, NeZero (q i)]
variable {ε L T C shell modLog level : ℝ} {K : Finset ι} {base : ∀ i, σ → ZMod (q i)}
variable {b : ℕ}
variable (hb : affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog ≤ b)

variable (p : FiniteProbabilityWeights Ω)

variable (F : Ω → ∀ i : {i // i ∉ K}, Option J × σ → ZMod (q i.val))

variable (sourceBase : ∀ i : {i // i ∉ K}, Option J × σ → ZMod (q i.val))

variable (siteBase : ∀ i : {i // i ∉ K}, σ → ZMod (q i.val))

variable {w rem : Ω → ℝ}

variable {cs : List (ProductCylinder (fun i : {i // i ∉ K} => Option J × σ → ZMod (q i.val)))}

variable (hchain : CylinderRemovalChain (primeCoordinateReference (σ := Option J × σ) (fun i : {i // i ∉ K} => q i.val)) sourceBase p F (2 : ℝ) (Real.exp (-T)) (affineRemovalDepth T) (affineComparisonTail ε L T) w rem cs)

variable (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1)

variable (hrem : ∀ z, 0 ≤ rem z ∧ rem z ≤ 1)

variable (hmass : p.mean rem ≤ (Real.exp (-T)))

variable (hstable : ResiduePrimeCoordinateStable g lo N M a q ((affineRemovalDepth T) + (affineComparisonTail ε L T)) (affineStabilityTolerance T) K base)

variable (hupper : PrimeRefinementUpperBound h g lo N M a q ((affineRemovalDepth T) + (affineComparisonTail ε L T)) level (affineIncrementTolerance L T) (affineStabilityTolerance T) K base)

variable (hM : 0 < M)

variable (hpair : Pairwise (fun i k => (q i).Coprime (q k)))

variable (hcop : ∀ i ∉ K, M.Coprime (q i))

variable (u : ResiduePrimeCoordinateCell lo N M a q K base)

variable (hg : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (g z).re ∧ (g z).re ≤ 1)

variable (hh : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1)

variable (hL : 0 ≤ L)

variable (hT : 0 ≤ T)

variable (hlower : Real.exp (-L) ≤ level)

variable (hsourceclose : ProductMarginalsClose (primeCoordinateReference (σ := Option J × σ) (fun i : {i // i ∉ K} => q i.val)) (observedProductDensity (primeCoordinateReference (σ := Option J × σ) (fun i : {i // i ∉ K} => q i.val)) p F (fun _ => 1)) (affineComparisonAccuracy (b) (affineComparisonScale ε L T C) L T)
      (max (((affineRemovalDepth T) + (affineComparisonTail ε L T)) * ((affineComparisonMoment (affineComparisonScale ε L T C)) + 1)) (2 * (b) + (affineRemovalDepth T))))

variable (prime power : ι → ℕ)

variable (hprime : ∀ i, (prime i).Prime)

variable (hpower : ∀ i, q i = prime i ^ power i)

variable (hJ : 2 ≤ Fintype.card J)

variable (hshell : 0 < shell)

variable (hlevel2 : level ≤ 2)

variable (hmodLog : 0 ≤ modLog)

variable (hmoduli : ∀ i ∉ K, (q i : ℝ) ≤ Real.exp modLog)

variable (hε : 0 < ε)
variable (hC : 0 ≤ C)
variable (hcount : (Fintype.card ι : ℝ) ≤ Real.exp C)
variable (hmandatory : affineMandatoryPrimes prime (ε / (2 + ε)) (affineComparisonScale ε L T C) ⊆ K)
variable (dimLog : ℝ)
variable (hdim : (Fintype.card σ : ℝ) ≤ Real.exp dimLog)
variable (hlength : ∀ k, Real.exp (modLog * (max (((affineRemovalDepth T) + (affineComparisonTail ε L T)) * ((affineComparisonMoment (affineComparisonScale ε L T C)) + 1)) (2 * (b) + (affineRemovalDepth T)) : ℕ) +
    affineComparisonAccuracyLog (b) (affineComparisonScale ε L T C) L T + dimLog + 1) ≤
    (residueIndexLength (lo k) (lo k + N k) (M.lcm (∏ i ∈ K, q i)) ((u.val k).val) : ℝ))

include hb p F sourceBase siteBase hchain hw hrem hmass hstable hupper hM hpair hcop u hg hh hL hT hlower hsourceclose prime power hprime hpower hJ hshell hlevel2 hmodLog hmoduli hε hC hcount hmandatory dimLog hdim hlength

theorem chosen_stable_residue_affine_total_at_degree_s2 :
    let density := fun f => residuePrimeCoordinateDensity lo N (M.lcm (∏ i ∈ K, q i))
      (fun k => (u.val k).val) (residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u)
      (fun i : {i // i ∉ K} => q i.val) f
    let μ := primeCoordinateReference (σ := Option J × σ) (fun i : {i // i ∉ K} => q i.val)
    affineResidueTruncatedPairing (J := J) (σ := σ) (fun i : {i // i ∉ K} => q i.val)
      (lowDegreeCoordinateSets {i // i ∉ K} (b)) (observedProductDensity μ p F w)
      (fun z => density (fun x => (h x).re) z - (1 + ε) * level * density (fun x => (g x).re) z) ≤
      level * (1 + 2 * ε) * (Real.exp (-T)) + shell / 16 + Real.sqrt (3 * (Real.exp (-T))) * (3 + (1 + ε) * level * 3) := by
  sorry

end

end Erdos3

end

end OAI
end
