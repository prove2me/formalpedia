-- Prove2me | Theorems.Thm_OAI_Erdos3_global_cutoff_initial_atom_comparison_s2
-- name    : OAI.Erdos3.global_cutoff_initial_atom_comparison_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:59:10.73885+00:00
-- url     : https://prove2.me/theorems/bc6f64aa-611b-4735-a9ac-18920ee5a18c
-- title:
--   Global-cutoff upper bound for the truncated pairing on one coupled atom
-- statement:
--   Let $\iota, \sigma, J$ be finite types with $\iota$ linearly ordered; let $h, g : \mathbb{Z}^\sigma \to \mathbb{C}$, $\mathrm{lo}, a : \sigma \to \mathbb{Z}$, $N : \sigma \to \mathbb{N}$, $M \in \mathbb{N}$ and $q : \iota \to \mathbb{N}$ with every $q_i \ne 0$; let $\varepsilon, L, T, C, \mathrm{shell}, \mathrm{modLog}, \mathrm{level} \in \mathbb{R}$, $K$ a finite subset of $\iota$, $\mathrm{base} \in \prod_i (\sigma \to \mathbb{Z}/q_i)$ and $A, B \in \mathbb{N}$. All of the following section hypotheses are part of the statement. Write $r_0 = $ `affineRemovalDepth T + affineComparisonTail ε L T` (a natural number). Assume: $|K| \le A$; $A + $ `affineComparisonDegree |Option J × σ| |σ| ε L T C shell modLog` $\le B$ (a natural-number degree budget); `ResiduePrimeCoordinateStable g lo N M a q r₀ (affineStabilityTolerance T) K base`; `PrimeRefinementUpperBound h g lo N M a q r₀ level (affineIncrementTolerance L T) (affineStabilityTolerance T) K base`; $0 < M$; an element `u` of `ResiduePrimeCoordinateCell lo N M a q K base` is given; $0 \le \mathrm{Re}\,g(z) \le 1$ and $0 \le \mathrm{Re}\,h(z) \le 1$ for $z$ in the box $X = \prod_k [\mathrm{lo}_k, \mathrm{lo}_k + N_k)$; $0 \le L$; $0 \le T$; $e^{-L} \le \mathrm{level}$; functions $\mathrm{prime}, \mathrm{power} : \iota \to \mathbb{N}$ with every $\mathrm{prime}(i)$ prime and $q_i = \mathrm{prime}(i)^{\mathrm{power}(i)}$; $2 \le |J|$; $0 < \mathrm{shell}$; $\mathrm{level} \le 2$; $0 \le \mathrm{modLog}$; $q_i \le e^{\mathrm{modLog}}$ for all $i$; $0 < \varepsilon$; $0 \le C$; $|\iota| \le e^{C}$; a real $\mathrm{dimLog}$ with $|\sigma| \le e^{\mathrm{dimLog}}$; for every $k \in \sigma$, $\exp($`affineComparisonLengthLog B ε L T C modLog dimLog`$)$ is at most `residueIndexLength` $(\mathrm{lo}_k, \mathrm{lo}_k + N_k, \mathrm{lcm}(M, \prod_{i \in K} q_i), u_k)$ (the number of integers in $[\mathrm{lo}_k, \mathrm{lo}_k + N_k)$ congruent to $u_k$ modulo that lcm); source data $\mathrm{sourceLo}, \mathrm{sourceA} : \mathrm{Option}\ J \times \sigma \to \mathbb{Z}$, $\mathrm{sourceN} : \mathrm{Option}\ J \times \sigma \to \mathbb{N}$, $\mathrm{sourceM} \in \mathbb{N}$, $\mathrm{sourceBase} \in \prod_i (\mathrm{Option}\ J \times \sigma \to \mathbb{Z}/q_i)$ and an element `sourceCell` of `ResiduePrimeCoordinateCell sourceLo sourceN sourceM sourceA q K sourceBase`; a function $w : \mathbb{Z}^{\mathrm{Option}\ J \times \sigma} \to \mathbb{R}$ with $0 \le w \le 1$ at every point of that source cell; $0 < \mathrm{sourceM}$; a real $\mathrm{sourceDimLog}$ with $|\mathrm{Option}\ J \times \sigma| \le e^{\mathrm{sourceDimLog}}$; the analogous length bound for the source cell with $\mathrm{sourceDimLog}$, $\mathrm{sourceM}$ and the coordinates of `sourceCell`; $\mathrm{prime}$ injective; $D \in \mathbb{N}$ and $\mathrm{parameterA} : J \to \mathbb{Z}$ with `affineSamplerPrimeMask prime (ε / (2 + ε)) (affineComparisonScale ε L T C) sourceM M D` $\subseteq K$ (a finite set of indices of $\iota$); and $A + $ `CyclicCrootSisask.spectralIterations shell` $(A(|\mathrm{Option}\ J \times \sigma|\,\mathrm{modLog} + |\sigma|\,\mathrm{modLog} + 1) + 4) \le B$ (a natural-number iteration count).
--
--   Put `c := affinePeriodProductCoupling q D parameterA` (a family, indexed by $i \in \iota$, of probability couplings between the uniform laws on $\mathrm{Option}\ J \times \sigma \to \mathbb{Z}/q_i$ and on $\sigma \to \mathbb{Z}/q_i$), `source := residuePrimeCoordinateDensity sourceLo sourceN sourceM sourceA _ q w` and, for $f : \mathbb{Z}^\sigma \to \mathbb{R}$, `site f := residuePrimeCoordinateDensity lo N M a _ q f` (densities, relative to the uniform product law on residues mod $q$, of the reductions mod $q$ of a uniform point of the residue box weighted by $w$, resp. $f$), and
--   $$\mathrm{factor} = \mathtt{productCouplingAtomMass}\ c\ K\ \mathrm{sourceBase}\ \mathrm{base} \cdot \mathtt{residuePrimeCoordinateMassRatio}(\mathrm{sourceLo}, \mathrm{sourceN}, \mathrm{sourceM}, \mathrm{sourceA}, q, K, \mathrm{sourceBase}) \cdot \mathtt{residuePrimeCoordinateMassRatio}(\mathrm{lo}, N, M, a, q, K, \mathrm{base}),$$
--   where `productCouplingAtomMass` is the mass under the product coupling of the fibre on $K$ at $(\mathrm{sourceBase}, \mathrm{base})$ and `residuePrimeCoordinateMassRatio` is the size of the cell divided by the size of the residue box and by the uniform fibre mass on $K$. Then `productAtomTruncatedPairing c (lowDegreeCoordinateSets ι B) K sourceBase base source F`, with $F(z) = $ `site (Re h)` $(z) - (1+\varepsilon)\,\mathrm{level}\cdot$ `site (Re g)` $(z)$, is at most
--   $$\mathrm{factor}\cdot\Big(\mathrm{level}(1+2\varepsilon)e^{-T} + \tfrac{\mathrm{shell}}{16} + \sqrt{3e^{-T}}\,\big(3 + 3(1+\varepsilon)\mathrm{level}\big)\Big) + (1 + (1+\varepsilon)\mathrm{level})\,\tfrac{\mathrm{shell}}{16}.$$
--   Here `lowDegreeCoordinateSets ι B` is the family of subsets of $\iota$ of size at most $B$, and `productAtomTruncatedPairing` is the pairing under the coupling `c` of the ANOVA truncations to that family of the source and site functions, each multiplied by the indicator of its fibre on $K$ at $\mathrm{sourceBase}$, resp. $\mathrm{base}$.
--
--   The hypotheses on cells use: `ResiduePrimeCoordinateCell lo N M a q K base`, the points of $X$ congruent to $a$ mod $M$ whose reduction mod $q_i$ equals $\mathrm{base}_i$ for $i \in K$; `ResiduePrimeCoordinateStable f … r δ K x`, which says that for every $J'$ disjoint from $K$ with $|J'| \le r$ and every $y$ agreeing with $x$ on $K$ whose $(K\cup J', y)$-cell is nonempty, the averages of $f$ over the $(K,x)$-cell and over the $(K\cup J', y)$-cell differ in norm by at most $\delta$; and `PrimeRefinementUpperBound h g … r level ε' δ K x`, which says that for the same $J', y$ the real part of the average of $h$ over the $(K \cup J', y)$-cell is at most $\mathrm{level}$ times the real part of the average of $g$ over the $(K,x)$-cell plus $\varepsilon' + \mathrm{level}\cdot\delta$. Also `affineStabilityTolerance T` $= e^{-(T+4)}$ and `affineIncrementTolerance L T` $= e^{-(L+T+4)}$.
--
--   Lean: `OAI.Erdos3.global_cutoff_initial_atom_comparison_s2`, which states OpenAI's `OAI.Erdos3.global_cutoff_initial_atom_comparison` (in `lean/OAI/Combinatorics/Progressions/Estimates/GlobalCutoffAtomComparison.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B218` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/GlobalCutoffAtomComparison.lean (declaration OAI.Erdos3.global_cutoff_initial_atom_comparison)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B218

section

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

section

variable {ι σ J : Type*} [Fintype J] [Fintype ι] [LinearOrder ι] [Fintype σ]
variable {h g : (σ → ℤ) → ℂ} {lo a : σ → ℤ} {N : σ → ℕ} {M : ℕ} {q : ι → ℕ}
variable [∀ i, NeZero (q i)]
variable {ε L T C shell modLog level : ℝ} {K : Finset ι} {base : ∀ i, σ → ZMod (q i)}
variable {A B : ℕ}
variable (hKcard : K.card ≤ A)
variable (hB : A + affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog ≤ B)

variable (hstable : ResiduePrimeCoordinateStable g lo N M a q ((affineRemovalDepth T) + (affineComparisonTail ε L T)) (affineStabilityTolerance T) K base)

variable (hupper : PrimeRefinementUpperBound h g lo N M a q ((affineRemovalDepth T) + (affineComparisonTail ε L T)) level (affineIncrementTolerance L T) (affineStabilityTolerance T) K base)

variable (hM : 0 < M)

variable (u : ResiduePrimeCoordinateCell lo N M a q K base)

variable (hg : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (g z).re ∧ (g z).re ≤ 1)

variable (hh : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1)

variable (hL : 0 ≤ L)

variable (hT : 0 ≤ T)

variable (hlower : Real.exp (-L) ≤ level)

variable (prime power : ι → ℕ)

variable (hprime : ∀ i, (prime i).Prime)

variable (hpower : ∀ i, q i = prime i ^ power i)

variable (hJ : 2 ≤ Fintype.card J)

variable (hshell : 0 < shell)

variable (hlevel2 : level ≤ 2)

variable (hmodLog : 0 ≤ modLog)

variable (hmoduli : ∀ i, (q i : ℝ) ≤ Real.exp modLog)

variable (hε : 0 < ε)
variable (hC : 0 ≤ C)
variable (hcount : (Fintype.card ι : ℝ) ≤ Real.exp C)
variable (dimLog : ℝ)
variable (hdim : (Fintype.card σ : ℝ) ≤ Real.exp dimLog)
variable (hlength : ∀ k, Real.exp (affineComparisonLengthLog B ε L T C modLog dimLog) ≤
    (residueIndexLength (lo k) (lo k + N k) (M.lcm (∏ i ∈ K, q i)) ((u.val k).val) : ℝ))

variable (sourceLo sourceA : Option J × σ → ℤ) (sourceN : Option J × σ → ℕ) (sourceM : ℕ)
variable (sourceBase : ∀ i, Option J × σ → ZMod (q i))
variable (sourceCell : ResiduePrimeCoordinateCell sourceLo sourceN sourceM sourceA q K sourceBase)
variable (w : (Option J × σ → ℤ) → ℝ)
variable (hw : ∀ z : ResiduePrimeCoordinateCell sourceLo sourceN sourceM sourceA q K sourceBase,
  0 ≤ w (fun k => (z.val k).val) ∧ w (fun k => (z.val k).val) ≤ 1)
variable (hsourceM : 0 < sourceM)
variable (sourceDimLog : ℝ)
variable (hsourceDim : (Fintype.card (Option J × σ) : ℝ) ≤ Real.exp sourceDimLog)
variable (hsourceLength : ∀ k, Real.exp (affineComparisonLengthLog B ε L T C modLog sourceDimLog) ≤
    (residueIndexLength (sourceLo k) (sourceLo k + sourceN k) (sourceM.lcm (∏ i ∈ K, q i)) ((sourceCell.val k).val) : ℝ))

variable (hinj : Function.Injective prime)
variable (D : ℕ) (parameterA : J → ℤ)
variable (hmask : affineSamplerPrimeMask prime (ε / (2 + ε)) (affineComparisonScale ε L T C) sourceM M D ⊆ K)
variable (hBinitial : A + CyclicCrootSisask.spectralIterations shell
  ((A : ℝ) * ((Fintype.card (Option J × σ) : ℝ) * modLog + (Fintype.card σ : ℝ) * modLog + 1) + 4) ≤ B)

include D parameterA hBinitial hKcard hB hstable hupper hM u hg hh hL hT hlower prime power hprime hpower hJ hshell hlevel2 hmodLog hmoduli hε hC hcount dimLog hdim hlength sourceLo sourceA sourceN sourceM sourceBase sourceCell w hw hsourceM sourceDimLog hsourceDim hsourceLength hinj hmask

theorem global_cutoff_initial_atom_comparison_s2 :
    let c := affinePeriodProductCoupling (σ := σ) q D parameterA
    let source := residuePrimeCoordinateDensity sourceLo sourceN sourceM sourceA ⟨sourceCell.val⟩ q w
    let site := fun f => residuePrimeCoordinateDensity lo N M a ⟨u.val⟩ q f
    let factor := productCouplingAtomMass c K sourceBase base *
      (residuePrimeCoordinateMassRatio sourceLo sourceN sourceM sourceA q K sourceBase *
        residuePrimeCoordinateMassRatio lo N M a q K base)
    productAtomTruncatedPairing c (lowDegreeCoordinateSets ι B) K sourceBase base source
      (fun z => site (fun x => (h x).re) z - (1 + ε) * level * site (fun x => (g x).re) z) ≤
      factor * (level * (1 + 2 * ε) * Real.exp (-T) + shell / 16 +
        Real.sqrt (3 * Real.exp (-T)) * (3 + (1 + ε) * level * 3)) +
      (1 + (1 + ε) * level) * (shell / 16) := by
  sorry

end

end Erdos3

end

end OAI
end
