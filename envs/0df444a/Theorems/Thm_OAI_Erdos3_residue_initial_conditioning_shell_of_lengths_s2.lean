-- Prove2me | Theorems.Thm_OAI_Erdos3_residue_initial_conditioning_shell_of_lengths_s2
-- name    : OAI.Erdos3.residue_initial_conditioning_shell_of_lengths_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:33:39.283024+00:00
-- url     : https://prove2.me/theorems/a628730f-8a33-4872-b2d2-c73fa49cc7de
-- title:
--   Initial conditioning shell for residue-box densities over coprime moduli, under explicit length bounds
-- statement:
--   Let $\iota, \sigma, \tau$ be finite types with decidable equality. For the "X side" let $\mathrm{lo}_X : \sigma \to \mathbb{Z}$, $N_X : \sigma \to \mathbb{N}$, $M_X \in \mathbb{N}$, $a_X : \sigma \to \mathbb{Z}$ be such that the residue box `IntegerResidueBox loX (loX + NX) MX aX` (the functions $z$ with $z_k \in [\mathrm{lo}_X(k), \mathrm{lo}_X(k) + N_X(k))$ and $z_k \equiv a_X(k) \pmod{M_X}$ for every $k \in \sigma$) is nonempty; similarly for the "Y side" with $\mathrm{lo}_Y, N_Y, M_Y, a_Y$ indexed by $\tau$. Let $q : \iota \to \mathbb{N}$ with every $q_i \ne 0$ and the $q_i$ pairwise coprime. Let $K \subseteq \iota$ be a finite set, $\mathrm{base}_X(i) : \sigma \to \mathbb{Z}/q_i$ and $\mathrm{base}_Y(i) : \tau \to \mathbb{Z}/q_i$ for each $i$, and let $u_X, u_Y$ be elements of the cells `ResiduePrimeCoordinateCell loX NX MX aX q K baseX` and `ResiduePrimeCoordinateCell loY NY MY aY q K baseY` (the points $z$ of the residue box with $z \bmod q_i = \mathrm{base}(i)$ for all $i \in K$; defined by OpenAI).
--
--   For each $i$ let $\mathrm{kernel}_i$ assign to each $x \in (\sigma \to \mathbb{Z}/q_i)$ probability weights on $\tau \to \mathbb{Z}/q_i$, and let $C : \iota \to \mathbb{R}$ with $C_i \ge 0$. Writing $\pi^\sigma_i, \pi^\tau_i$ for the uniform probability weights on $\sigma \to \mathbb{Z}/q_i$ and $\tau \to \mathbb{Z}/q_i$ (`primeCoordinateReference`), suppose for all $i$:
--   - for every $f$ on $\tau \to \mathbb{Z}/q_i$ with $\mathbb{E}_{\pi^\tau_i} f = 0$: $\ \mathbb{E}_{x \sim \pi^\sigma_i}\bigl[(\mathbb{E}_{\mathrm{kernel}_i(x)} f)^2\bigr] \le C_i\,\mathbb{E}_{\pi^\tau_i}[f^2]$;
--   - for every $f$: $\ \mathbb{E}_{x \sim \pi^\sigma_i}\bigl[\mathbb{E}_{\mathrm{kernel}_i(x)} f\bigr] = \mathbb{E}_{\pi^\tau_i} f$.
--
--   Let $w : (\sigma \to \mathbb{Z}) \to \mathbb{R}$, $f : (\tau \to \mathbb{Z}) \to \mathbb{R}$, and $B \in \mathbb{N}$ with $|K| \le B$. Let $\kappa$ be real with $0 \le \kappa \le 1$ and $C_i \le \kappa^2$ for all $i \notin K$. Suppose $M_X > 0$, $M_Y > 0$, $M_X$ and $M_Y$ are coprime to $q_i$ for every $i \notin K$, $0 \le w(z) \le 1$ for every $z$ in the X cell (as an integer vector), and $0 \le f(z) \le 1$ for every $z$ in the Y cell. Let $P, \mathrm{modLog}, \mathrm{dim}_X, \mathrm{dim}_Y$ be real with $P \ge 0$, $\mathrm{modLog} \ge 0$, $|\iota| \le e^{P}$, $q_i \le e^{\mathrm{modLog}}$ for $i \notin K$, $|\sigma| \le e^{\mathrm{dim}_X}$, $|\tau| \le e^{\mathrm{dim}_Y}$, and for every coordinate $k$,
--   $$\exp\bigl(\mathrm{modLog}\cdot 2B + \texttt{affineComparisonAccuracyLog}\ B\ P\ 0\ 0 + \mathrm{dim}_X + 1\bigr) \le \texttt{residueIndexLength}\bigl(\mathrm{lo}_X(k), \mathrm{lo}_X(k) + N_X(k), \mathrm{lcm}(M_X, \textstyle\prod_{i \in K} q_i), u_X(k)\bigr),$$
--   and the same on the Y side with $\mathrm{dim}_Y$ and $u_Y$; here `affineComparisonAccuracyLog B P 0 0` $= (P+3)^3 + 2B(P + 2) + 4$ and `residueIndexLength a b r v` is the number of integers $j$ with $a \le v + rj < b$ (defined by OpenAI).
--
--   Let $c_i$ = `FiniteProbabilityCoupling.ofKernel` $(\pi^\sigma_i, \pi^\tau_i, \mathrm{kernel}_i)$ (the coupling with law $x \mapsto \pi^\sigma_i(x)\,\mathrm{kernel}_i(x)$), $\mathcal{L}_B$ = `lowDegreeCoordinateSets ι B` (subsets of size at most $B$), $\rho_X$ = `residuePrimeCoordinateMassRatio loX NX MX aX q K baseX` and $\rho_Y$ likewise (the relative density of the cell in the box divided by the reference mass of the residue condition). Then
--   $$\Bigl| \Pi - \alpha\cdot\bigl(\rho_X\,\rho_Y\cdot \Pi'\bigr) \Bigr| \le 2^{|K|}\bigl(\kappa^{B - |K|}\,(3\rho_X)(3\rho_Y)\bigr),$$
--   where
--   - $\Pi$ = `productAtomTruncatedPairing c 𝓛_B K baseX baseY (residuePrimeCoordinateDensity loX NX MX aX hneX q w) (residuePrimeCoordinateDensity loY NY MY aY hneY q f)` (the pairing under the product coupling of the $\mathcal{L}_B$-ANOVA truncations of the residue-observed densities of $w$ and $f$, each restricted to its atom $\mathrm{base}$ on the coordinates in $K$);
--   - $\alpha$ = `productCouplingAtomMass c K baseX baseY`;
--   - $\Pi'$ = `productTruncatedPairing (fun i : {i // i ∉ K} => c i) (lowDegreeCoordinateSets {i // i ∉ K} (B - |K|)) (residueCellOutsideDensity loX NX MX aX q K baseX uX w) (residueCellOutsideDensity loY NY MY aY q K baseY uY f)` (the analogous pairing over the coordinates outside $K$, for the densities of $w$, $f$ observed on the cells).
--   All named functions are defined by OpenAI.
--
--   Lean: `OAI.Erdos3.residue_initial_conditioning_shell_of_lengths_s2`, which states OpenAI's `OAI.Erdos3.residue_initial_conditioning_shell_of_lengths` (in `lean/OAI/Combinatorics/Progressions/Lattices/AffineMaskedInitialShell.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B193`, `OAIE3v2B197` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AffineMaskedInitialShell.lean (declaration OAI.Erdos3.residue_initial_conditioning_shell_of_lengths)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B193
import Definitions.Def_OAIE3v2B197

section

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem residue_initial_conditioning_shell_of_lengths_s2 {ι σ τ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]
    (loX : σ → ℤ) (NX : σ → ℕ) (MX : ℕ) (aX : σ → ℤ)
    (hneX : Nonempty (IntegerResidueBox loX (fun k => loX k + NX k) (fun _ => (MX : ℤ)) aX))
    (loY : τ → ℤ) (NY : τ → ℕ) (MY : ℕ) (aY : τ → ℤ)
    (hneY : Nonempty (IntegerResidueBox loY (fun k => loY k + NY k) (fun _ => (MY : ℤ)) aY))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (hpair : Pairwise (fun i k => (q i).Coprime (q k)))
    (K : Finset ι) (baseX : ∀ i, σ → ZMod (q i)) (baseY : ∀ i, τ → ZMod (q i))
    (uX : ResiduePrimeCoordinateCell loX NX MX aX q K baseX)
    (uY : ResiduePrimeCoordinateCell loY NY MY aY q K baseY)
    (kernel : ∀ i, (σ → ZMod (q i)) → FiniteProbabilityWeights (τ → ZMod (q i)))
    (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i (f : (τ → ZMod (q i)) → ℝ), (primeCoordinateReference (σ := τ) q i).mean f = 0 →
      (primeCoordinateReference (σ := σ) q i).mean (fun x => (kernel i x).mean f ^ 2) ≤
        C i * (primeCoordinateReference (σ := τ) q i).mean (fun y => f y ^ 2))
    (hmean : ∀ i (f : (τ → ZMod (q i)) → ℝ),
      (primeCoordinateReference (σ := σ) q i).mean (fun x => (kernel i x).mean f) =
        (primeCoordinateReference (σ := τ) q i).mean f)
    (w : (σ → ℤ) → ℝ) (f : (τ → ℤ) → ℝ) (B : ℕ) (hKB : K.card ≤ B)
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hcap : ∀ i ∉ K, C i ≤ κ ^ 2)
    (hMX : 0 < MX) (hMY : 0 < MY)
    (hcopX : ∀ i ∉ K, MX.Coprime (q i)) (hcopY : ∀ i ∉ K, MY.Coprime (q i))
    (hw : ∀ z : ResiduePrimeCoordinateCell loX NX MX aX q K baseX,
      0 ≤ w (fun k => (z.val k).val) ∧ w (fun k => (z.val k).val) ≤ 1)
    (hf : ∀ z : ResiduePrimeCoordinateCell loY NY MY aY q K baseY,
      0 ≤ f (fun k => (z.val k).val) ∧ f (fun k => (z.val k).val) ≤ 1)
    (P modLog dimX dimY : ℝ) (hP : 0 ≤ P) (hmodLog : 0 ≤ modLog)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P)
    (hmoduli : ∀ i ∉ K, (q i : ℝ) ≤ Real.exp modLog)
    (hdimX : (Fintype.card σ : ℝ) ≤ Real.exp dimX) (hdimY : (Fintype.card τ : ℝ) ≤ Real.exp dimY)
    (hlengthX : ∀ k, Real.exp (modLog * (2 * B : ℕ) + affineComparisonAccuracyLog B P 0 0 + dimX + 1) ≤
      (residueIndexLength (loX k) (loX k + NX k) (MX.lcm (∏ i ∈ K, q i)) ((uX.val k).val) : ℝ))
    (hlengthY : ∀ k, Real.exp (modLog * (2 * B : ℕ) + affineComparisonAccuracyLog B P 0 0 + dimY + 1) ≤
      (residueIndexLength (loY k) (loY k + NY k) (MY.lcm (∏ i ∈ K, q i)) ((uY.val k).val) : ℝ)) :
    let c := fun i => FiniteProbabilityCoupling.ofKernel (primeCoordinateReference (σ := σ) q i)
      (primeCoordinateReference (σ := τ) q i) (kernel i) (hmean i)
    |productAtomTruncatedPairing c (lowDegreeCoordinateSets ι B) K baseX baseY
        (residuePrimeCoordinateDensity loX NX MX aX hneX q w) (residuePrimeCoordinateDensity loY NY MY aY hneY q f) -
      productCouplingAtomMass c K baseX baseY *
        (residuePrimeCoordinateMassRatio loX NX MX aX q K baseX * residuePrimeCoordinateMassRatio loY NY MY aY q K baseY *
          productTruncatedPairing (fun i : {i // i ∉ K} => c i.val)
            (lowDegreeCoordinateSets {i // i ∉ K} (B - K.card))
            (residueCellOutsideDensity loX NX MX aX q K baseX uX w)
            (residueCellOutsideDensity loY NY MY aY q K baseY uY f))| ≤
      (2 : ℝ) ^ K.card * (κ ^ (B - K.card) *
        (residuePrimeCoordinateMassRatio loX NX MX aX q K baseX * 3) *
        (residuePrimeCoordinateMassRatio loY NY MY aY q K baseY * 3)) := by
  sorry

end Erdos3

end

end OAI
end
