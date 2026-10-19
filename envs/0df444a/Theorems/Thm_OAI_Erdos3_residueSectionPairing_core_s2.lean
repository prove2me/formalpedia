-- Prove2me | Theorems.Thm_OAI_Erdos3_residueSectionPairing_core_s2
-- name    : OAI.Erdos3.residueSectionPairing_core_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:33:22.92091+00:00
-- url     : https://prove2.me/theorems/ec7fced6-70e0-4359-8c6b-9b497f4043ce
-- title:
--   The core truncated coupling pairing of two prime-coordinate section averages factors through the residue cells
-- statement:
--   All named objects below are defined by OpenAI. Let $\iota$, $\sigma$, $\tau$ be finite types with decidable equality. On the $X$ side let $\mathrm{lo}_X : \sigma \to \mathbb{Z}$, $N_X : \sigma \to \mathbb{N}$, $M_X \in \mathbb{N}$ and $a_X : \sigma \to \mathbb{Z}$, such that the residue box `IntegerResidueBox` $\mathcal{R}_X = \prod_{k \in \sigma}\{x \in [\mathrm{lo}_X(k), \mathrm{lo}_X(k) + N_X(k)) : x \equiv a_X(k) \pmod{M_X}\}$ is nonempty; likewise on the $Y$ side $\mathrm{lo}_Y, N_Y, M_Y, a_Y$ indexed by $\tau$, with $\mathcal{R}_Y$ nonempty. Let $q : \iota \to \mathbb{N}$ be pairwise coprime nonzero moduli, $K \subseteq \iota$ a finite set, and `baseX` $\in \prod_{i} (\mathbb{Z}/q_i)^\sigma$, `baseY` $\in \prod_i (\mathbb{Z}/q_i)^\tau$. Let $u_X$ be an element of `ResiduePrimeCoordinateCell loX NX MX aX q K baseX` (the set of $z \in \mathcal{R}_X$ with $z \bmod q_i = \mathrm{baseX}_i$ for all $i \in K$), and $u_Y$ an element of the analogous cell on the $Y$ side. For each $i \in \iota$ let $c_i$ be a coupling (`FiniteProbabilityCoupling`) of the uniform distributions on $(\mathbb{Z}/q_i)^\sigma$ and on $(\mathbb{Z}/q_i)^\tau$ (`primeCoordinateReference`). Let $w : \mathbb{Z}^\sigma \to \mathbb{R}$, $f : \mathbb{Z}^\tau \to \mathbb{R}$ and $B \in \mathbb{N}$.
--
--   Write $\rho_w$ = `residuePrimeCoordinateDensity loX NX MX aX hneX q w` for the density, with respect to the product of uniform distributions on $\prod_i (\mathbb{Z}/q_i)^\sigma$, of the pushforward of $w$ times the uniform distribution on $\mathcal{R}_X$ under the reduction map $z \mapsto (z \bmod q_i)_i$; similarly $\rho_f$ on the $Y$ side. In general `productSectionAverage μ T A z g` is the function $x \mapsto \mathbb{E}_y\, g\bigl(\mathrm{mix}_T(\mathrm{mix}_A(z, y), x)\bigr)$, with $y$ distributed according to the product reference measure $\prod_i \mu_i$, where $\mathrm{mix}_S(a, b)$ is the point equal to $a$ on $S$ and to $b$ elsewhere. For $T = A = K$ and $z = $ base the average over $y$ is trivial: `productSectionAverage μ K K base g` is the function $x \mapsto g(\text{the point equal to base on } K \text{ and to } x \text{ elsewhere})$, which depends only on the coordinates of $x$ outside $K$. Then
--   $$\texttt{productTruncatedPairing}\ c\ (\texttt{conditioningCoreSupports}\ K\ B)\ \bigl(\mathrm{SA}_X(\rho_w)\bigr)\ \bigl(\mathrm{SA}_Y(\rho_f)\bigr) = r_X\, r_Y\cdot \texttt{productTruncatedPairing}\ (c|_{\iota \setminus K})\ (\texttt{lowDegreeCoordinateSets}\ (\iota\setminus K)\ (B - |K|))\ \rho^{\mathrm{out}}_w\ \rho^{\mathrm{out}}_f,$$
--   where:
--   - $\mathrm{SA}_X(\rho_w)$ = `productSectionAverage (primeCoordinateReference q) K K baseX ρ_w`, and similarly $\mathrm{SA}_Y(\rho_f)$ with `baseY`;
--   - `productTruncatedPairing c D g h` is the expectation, under the product of the couplings $c_i$, of $\tilde g(x)\,\tilde h(y)$, where $\tilde g$ and $\tilde h$ are the ANOVA truncations of $g$ and $h$ to the coordinate sets in $D$ (sums of their ANOVA components over $S \in D$);
--   - `conditioningCoreSupports K B` is the family of subsets of $\iota \setminus K$ of cardinality at most $B - |K|$ (truncated subtraction), and `lowDegreeCoordinateSets (ι∖K) (B - |K|)` is the family of all subsets of $\iota \setminus K$ (as a subtype) of cardinality at most $B - |K|$;
--   - $r_X$ = `residuePrimeCoordinateMassRatio loX NX MX aX q K baseX` $= \dfrac{|\text{cell}_X|/|\mathcal{R}_X|}{\text{product-reference mass of the fiber } \{x : x_i = \mathrm{baseX}_i \ \forall i \in K\}}$, and similarly $r_Y$;
--   - $\rho^{\mathrm{out}}_w$ = `residueCellOutsideDensity loX NX MX aX q K baseX uX w` is the density, with respect to the uniform distributions on $(\mathbb{Z}/q_i)^\sigma$ for $i \notin K$, of the pushforward of $w$ times the uniform distribution on the cell $\text{cell}_X$ under reduction modulo the $q_i$ with $i \notin K$; similarly $\rho^{\mathrm{out}}_f$.
--
--   Lean: `OAI.Erdos3.residueSectionPairing_core_s2`, which states OpenAI's `OAI.Erdos3.residueSectionPairing_core` (in `lean/OAI/Combinatorics/Progressions/Lattices/AffineMaskedInitialShell.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B193`, `OAIE3v2B197` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AffineMaskedInitialShell.lean (declaration OAI.Erdos3.residueSectionPairing_core)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B193
import Definitions.Def_OAIE3v2B197

section

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem residueSectionPairing_core_s2 {ι σ τ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
    (loX : σ → ℤ) (NX : σ → ℕ) (MX : ℕ) (aX : σ → ℤ)
    (hneX : Nonempty (IntegerResidueBox loX (fun k => loX k + NX k) (fun _ => (MX : ℤ)) aX))
    (loY : τ → ℤ) (NY : τ → ℕ) (MY : ℕ) (aY : τ → ℤ)
    (hneY : Nonempty (IntegerResidueBox loY (fun k => loY k + NY k) (fun _ => (MY : ℤ)) aY))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (hpair : Pairwise (fun i k => (q i).Coprime (q k)))
    (K : Finset ι) (baseX : ∀ i, σ → ZMod (q i)) (baseY : ∀ i, τ → ZMod (q i))
    (uX : ResiduePrimeCoordinateCell loX NX MX aX q K baseX)
    (uY : ResiduePrimeCoordinateCell loY NY MY aY q K baseY)
    (c : ∀ i, FiniteProbabilityCoupling (primeCoordinateReference (σ := σ) q i) (primeCoordinateReference (σ := τ) q i))
    (w : (σ → ℤ) → ℝ) (f : (τ → ℤ) → ℝ) (B : ℕ) :
    productTruncatedPairing c (conditioningCoreSupports K B)
      (productSectionAverage (primeCoordinateReference (σ := σ) q) K K baseX (residuePrimeCoordinateDensity loX NX MX aX hneX q w))
      (productSectionAverage (primeCoordinateReference (σ := τ) q) K K baseY (residuePrimeCoordinateDensity loY NY MY aY hneY q f)) =
      residuePrimeCoordinateMassRatio loX NX MX aX q K baseX * residuePrimeCoordinateMassRatio loY NY MY aY q K baseY *
        productTruncatedPairing (fun i : {i // i ∉ K} => c i.val)
          (lowDegreeCoordinateSets {i // i ∉ K} (B - K.card))
          (residueCellOutsideDensity loX NX MX aX q K baseX uX w)
          (residueCellOutsideDensity loY NY MY aY q K baseY uY f) := by
  sorry

end Erdos3

end

end OAI
end
