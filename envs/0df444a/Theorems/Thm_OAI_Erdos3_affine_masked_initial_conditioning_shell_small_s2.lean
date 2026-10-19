-- Prove2me | Theorems.Thm_OAI_Erdos3_affine_masked_initial_conditioning_shell_small_s2
-- name    : OAI.Erdos3.affine_masked_initial_conditioning_shell_small_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:48:28.231983+00:00
-- url     : https://prove2.me/theorems/6694e21e-2b20-4dab-98ed-6b3a779da320
-- title:
--   Conditioning the low-degree truncated affine pairing on a masked prime-coordinate atom changes it by at most shell/16
-- statement:
--   All named objects below are defined by OpenAI.
--
--   **Data.** Let $\iota, J, \sigma$ be finite types ($\iota$ with decidable equality). For the source side, let $\mathrm{lo}_X : \mathrm{Option}\ J \times \sigma \to \mathbb{Z}$, $N_X : \mathrm{Option}\ J \times \sigma \to \mathbb{N}$, $M_X \in \mathbb{N}$, $a_X : \mathrm{Option}\ J \times \sigma \to \mathbb{Z}$, such that the residue box $\mathcal{R}_X$ = `IntegerResidueBox loX (loX + NX) MX aX` (arrays $z$ with $z_k \in [\mathrm{lo}_X(k), \mathrm{lo}_X(k) + N_X(k))$ and $z_k \equiv a_X(k) \pmod{M_X}$) is nonempty. Similarly for the site side, $\mathrm{lo}_Y, N_Y, M_Y, a_Y$ indexed by $\sigma$ with nonempty residue box $\mathcal{R}_Y$. Let $q : \iota \to \mathbb{N}$ with all $q_i \ge 1$, $K \subseteq \iota$ a finite set, base residues `baseX i : Option J × σ → ZMod (q i)` and `baseY i : σ → ZMod (q i)`, and points $u_X$ of `ResiduePrimeCoordinateCell loX NX MX aX q K baseX` (elements $z \in \mathcal{R}_X$ with $z \bmod q_i$ = `baseX i` for every $i \in K$) and $u_Y$ of the analogous cell for $Y$. Let $D \in \mathbb{N}$, $a : J \to \mathbb{Z}$, and `prime, power : ι → ℕ` with every $\mathrm{prime}_i$ prime, $q_i = \mathrm{prime}_i^{\mathrm{power}_i}$, and `prime` injective. Assume $|J| \ge 2$. Let $w : \mathbb{Z}^{\mathrm{Option}\ J \times \sigma} \to \mathbb{R}$, $f : \mathbb{Z}^{\sigma} \to \mathbb{R}$, and $B \in \mathbb{N}$.
--
--   **Hypotheses.** $M_X > 0$, $M_Y > 0$; $0 \le w(z) \le 1$ for every $z$ in the $X$-cell and $0 \le f(z) \le 1$ for every $z$ in the $Y$-cell (values taken at the underlying integer arrays); reals $P, \mathrm{modLog}, \dim_X, \dim_Y$ with $P \ge 0$, $\mathrm{modLog} \ge 0$; a real $\xi > 0$ with `affineSamplerPrimeMask prime ξ P MX MY D` $\subseteq K$; $|\iota| \le e^{P}$; $q_i \le e^{\mathrm{modLog}}$ for all $i$; $|\mathrm{Option}\ J \times \sigma| \le e^{\dim_X}$ and $|\sigma| \le e^{\dim_Y}$; for every coordinate $k$,
--   $$\exp\bigl(\mathrm{modLog}\cdot 2B + \texttt{affineComparisonAccuracyLog}\ B\ P\ 0\ 0 + \dim_X + 1\bigr) \le \texttt{residueIndexLength}\bigl(\mathrm{lo}_X(k),\ \mathrm{lo}_X(k) + N_X(k),\ \operatorname{lcm}(M_X, \textstyle\prod_{i \in K} q_i),\ u_X(k)\bigr),$$
--   and likewise for $Y$ with $\dim_Y$, $M_Y$, $u_Y$ (`residueIndexLength a b r v` is the number of integers in $[a, b)$ congruent to $v$ mod $r$); a real $\mathrm{shell} > 0$ with
--   $$|K| + \texttt{CyclicCrootSisask.spectralIterations}\ \mathrm{shell}\ \bigl(|K|\,(|\mathrm{Option}\ J\times\sigma|\,\mathrm{modLog} + |\sigma|\,\mathrm{modLog} + 1) + 4\bigr) \le B.$$
--
--   **Statement.** Let $c$ = `affinePeriodProductCoupling q D a` (for each $i$, a coupling of the uniform reference laws on residues mod $q_i$ of $X$- and $Y$-arrays). Then
--   $$\Bigl| \Pi_c - m_c\cdot\bigl(\rho_X\,\rho_Y\cdot \Pi^{\mathrm{out}}\bigr)\Bigr| \le \frac{\mathrm{shell}}{16},$$
--   where:
--   - $\Pi_c$ = `productAtomTruncatedPairing c (lowDegreeCoordinateSets ι B) K baseX baseY dX dY`, the pairing under $c$ of the ANOVA truncations to coordinate sets of size at most $B$ of $\mathbf{1}_{\text{atom}}\cdot d_X$ and $\mathbf{1}_{\text{atom}}\cdot d_Y$, with atom the fiber over `baseX`, `baseY` on $K$, and $d_X$ = `residuePrimeCoordinateDensity loX NX MX aX hneX q w`, $d_Y$ = `residuePrimeCoordinateDensity loY NY MY aY hneY q f` (the densities, with respect to the reference product laws, of the residue observations of $w$ and $f$ under the uniform law on the boxes);
--   - $m_c$ = `productCouplingAtomMass c K baseX baseY`, the mass of that atom under the product of the couplings;
--   - $\rho_X$ = `residuePrimeCoordinateMassRatio loX NX MX aX q K baseX` $= |\text{cell}_X|/|\mathcal{R}_X|$ divided by the reference mass of the fiber, and $\rho_Y$ likewise;
--   - $\Pi^{\mathrm{out}}$ = `affineResidueTruncatedPairing (fun i : {i // i ∉ K} => q i) (lowDegreeCoordinateSets {i // i ∉ K} (B - |K|)) (residueCellOutsideDensity loX NX MX aX q K baseX uX w) (residueCellOutsideDensity loY NY MY aY q K baseY uY f)`, the truncated pairing (to sets of size at most $B - |K|$, natural subtraction) of the outside-$K$ residue densities of $w$ and $f$ conditioned on the cells, under the affine sample product coupling.
--
--   Lean: `OAI.Erdos3.affine_masked_initial_conditioning_shell_small_s2`, which states OpenAI's `OAI.Erdos3.affine_masked_initial_conditioning_shell_small` (in `lean/OAI/Combinatorics/Progressions/Lattices/AffineMaskedInitialShell.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B218` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AffineMaskedInitialShell.lean (declaration OAI.Erdos3.affine_masked_initial_conditioning_shell_small)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B218

section

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem affine_masked_initial_conditioning_shell_small_s2 {ι J σ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype J] [Fintype σ]
    (loX : (Option J × σ) → ℤ) (NX : (Option J × σ) → ℕ) (MX : ℕ) (aX : (Option J × σ) → ℤ)
    (hneX : Nonempty (IntegerResidueBox loX (fun k => loX k + NX k) (fun _ => (MX : ℤ)) aX))
    (loY : σ → ℤ) (NY : σ → ℕ) (MY : ℕ) (aY : σ → ℤ)
    (hneY : Nonempty (IntegerResidueBox loY (fun k => loY k + NY k) (fun _ => (MY : ℤ)) aY))
    (q : ι → ℕ) [∀ i, NeZero (q i)]
    (K : Finset ι) (baseX : ∀ i, (Option J × σ) → ZMod (q i)) (baseY : ∀ i, σ → ZMod (q i))
    (uX : ResiduePrimeCoordinateCell loX NX MX aX q K baseX)
    (uY : ResiduePrimeCoordinateCell loY NY MY aY q K baseY)
    (D : ℕ) (a : J → ℤ)
    (prime power : ι → ℕ) (hprime : ∀ i, (prime i).Prime)
    (hpower : ∀ i, q i = prime i ^ power i) (hinj : Function.Injective prime) (hJ : 2 ≤ Fintype.card J)
    (w : ((Option J × σ) → ℤ) → ℝ) (f : (σ → ℤ) → ℝ) (B : ℕ)
    (hMX : 0 < MX) (hMY : 0 < MY)
    (hw : ∀ z : ResiduePrimeCoordinateCell loX NX MX aX q K baseX,
      0 ≤ w (fun k => (z.val k).val) ∧ w (fun k => (z.val k).val) ≤ 1)
    (hf : ∀ z : ResiduePrimeCoordinateCell loY NY MY aY q K baseY,
      0 ≤ f (fun k => (z.val k).val) ∧ f (fun k => (z.val k).val) ≤ 1)
    (P modLog dimX dimY : ℝ) (hP : 0 ≤ P) (hmodLog : 0 ≤ modLog)
    (ξ : ℝ) (hξ : 0 < ξ) (hmask : affineSamplerPrimeMask prime ξ P MX MY D ⊆ K)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P)
    (hmoduli : ∀ i, (q i : ℝ) ≤ Real.exp modLog)
    (hdimX : (Fintype.card (Option J × σ) : ℝ) ≤ Real.exp dimX) (hdimY : (Fintype.card σ : ℝ) ≤ Real.exp dimY)
    (hlengthX : ∀ k, Real.exp (modLog * (2 * B : ℕ) + affineComparisonAccuracyLog B P 0 0 + dimX + 1) ≤
      (residueIndexLength (loX k) (loX k + NX k) (MX.lcm (∏ i ∈ K, q i)) ((uX.val k).val) : ℝ))
    (hlengthY : ∀ k, Real.exp (modLog * (2 * B : ℕ) + affineComparisonAccuracyLog B P 0 0 + dimY + 1) ≤
      (residueIndexLength (loY k) (loY k + NY k) (MY.lcm (∏ i ∈ K, q i)) ((uY.val k).val) : ℝ))
    (shell : ℝ) (hshell : 0 < shell)
    (hB : K.card + CyclicCrootSisask.spectralIterations shell
      ((K.card : ℝ) * ((Fintype.card (Option J × σ) : ℝ) * modLog + (Fintype.card σ : ℝ) * modLog + 1) + 4) ≤ B) :
    let c := affinePeriodProductCoupling (σ := σ) q D a
    |productAtomTruncatedPairing c (lowDegreeCoordinateSets ι B) K baseX baseY
        (residuePrimeCoordinateDensity loX NX MX aX hneX q w) (residuePrimeCoordinateDensity loY NY MY aY hneY q f) -
      productCouplingAtomMass c K baseX baseY *
        (residuePrimeCoordinateMassRatio loX NX MX aX q K baseX * residuePrimeCoordinateMassRatio loY NY MY aY q K baseY *
          affineResidueTruncatedPairing (J := J) (σ := σ) (fun i : {i // i ∉ K} => q i.val)
            (lowDegreeCoordinateSets {i // i ∉ K} (B - K.card))
            (residueCellOutsideDensity loX NX MX aX q K baseX uX w)
            (residueCellOutsideDensity loY NY MY aY q K baseY uY f))| ≤ shell / 16 := by
  sorry

end Erdos3

end

end OAI
end
