-- Prove2me | Theorems.Thm_OAI_Erdos3_residue_initial_conditioning_shell_s2
-- name    : OAI.Erdos3.residue_initial_conditioning_shell_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:33:37.764378+00:00
-- url     : https://prove2.me/theorems/8bdd7e9c-237e-4487-9640-9b953c640742
-- title:
--   Initial conditioning shell estimate for low-degree pairings of residue-box densities over coprime prime coordinates
-- statement:
--   Let $\iota, \sigma, \tau$ be finite types with decidable equality. We use the following OpenAI definitions, stated for $\sigma$ (the same apply to $\tau$).
--   - For $\mathrm{lo} : \sigma \to \mathbb{Z}$, $N : \sigma \to \mathbb{N}$, $M \in \mathbb{N}$ and $a : \sigma \to \mathbb{Z}$, the residue box `IntegerResidueBox lo (lo + N) M a` is the finite set of tuples $z \in \mathbb{Z}^{\sigma}$ with $\mathrm{lo}_k \le z_k < \mathrm{lo}_k + N_k$ and $z_k \equiv a_k \pmod M$ for all $k$.
--   - For moduli $q : \iota \to \mathbb{N}$ (all nonzero), `primeCoordinateReference q i` is the uniform probability distribution on $(\mathbb{Z}/q_i\mathbb{Z})^{\sigma}$; the product over $i$ of these is denoted $\pi_\sigma$. The observation of $z \in \mathbb{Z}^{\sigma}$ is the tuple $(z \bmod q_i)_{i \in \iota}$.
--   - `residuePrimeCoordinateDensity lo N M a hne q f` (for $f : \mathbb{Z}^{\sigma} \to \mathbb{R}$ and a proof that the box is nonempty) is the function on $\prod_i (\mathbb{Z}/q_i\mathbb{Z})^{\sigma}$ whose value at $y$ is $\mathbb{E}_{z}\bigl[f(z)\,\mathbf{1}\{\text{observation of } z = y\}\bigr] / \pi_\sigma(y)$, with $z$ uniform on the residue box.
--   - For $K \subseteq \iota$ and $\mathrm{base} \in \prod_i (\mathbb{Z}/q_i\mathbb{Z})^{\sigma}$, a `ResiduePrimeCoordinateCell lo N M a q K base` is a point $z$ of the residue box with $z \bmod q_i = \mathrm{base}_i$ for every $i \in K$. Given such a cell point $u$, `residueCellOutsideDensity lo N M a q K base u f` is the analogous density on $\prod_{i \notin K} (\mathbb{Z}/q_i\mathbb{Z})^{\sigma}$: $z$ is uniform on the set of cell points, only the residues at the indices $i \notin K$ are observed, and the reference is the uniform distribution there (the point $u$ only witnesses that the cell is nonempty).
--   - `residuePrimeCoordinateMassRatio lo N M a q K base` is (number of cell points)/(number of box points) divided by the $\pi_\sigma$-mass of the set of $y$ with $y_i = \mathrm{base}_i$ for all $i \in K$.
--   - For probability weights $\mu_i, \nu_i$ and couplings $c_i$ of them, `productTruncatedPairing c 𝒟 w f` is `productCouplingPairing c (productANOVATruncation μ 𝒟 w) (productANOVATruncation ν 𝒟 f)`, and `productAtomTruncatedPairing c 𝒟 K x y w f` is the same with $w, f$ replaced by $z \mapsto \mathbf{1}\{z_i = x_i\ \forall i \in K\}\,w(z)$ and $z \mapsto \mathbf{1}\{z_i = y_i\ \forall i \in K\}\,f(z)$. Here `productCouplingPairing c F G` is the mean of $F(z_1)G(z_2)$ under the product of the couplings, and `productANOVATruncation μ 𝒟 F` $= \sum_{S \in \mathcal{D}} F_S$ with $F_S(x) = \sum_{U \subseteq S} (-1)^{|U|}\,\mathbb{E}_{y \sim \prod \mu_i} F(x|_{S \setminus U}, y|_{\text{rest}})$ the ANOVA component.
--   - `productANOVAEnergy μ 𝒟 F` $= \sum_{S \in \mathcal{D}} \mathbb{E}_{x \sim \prod\mu_i}\, F_S(x)^2$; `lowDegreeCoordinateSets T B` is the family of subsets of $T$ with at most $B$ elements; `productCouplingAtomMass c K x y` is the mass, under the product of the couplings, of the pairs $(z_1, z_2)$ with $(z_1)_i = x_i$ and $(z_2)_i = y_i$ for all $i \in K$.
--   - `FiniteProbabilityCoupling.ofKernel p q κ h` is the coupling of $p$ and $q$ with joint weights $p(x)\,\kappa(x)(y)$.
--
--   Now let $\mathrm{lo}_X : \sigma \to \mathbb{Z}$, $N_X : \sigma \to \mathbb{N}$, $M_X \in \mathbb{N}$, $a_X : \sigma \to \mathbb{Z}$ with the residue box $\mathrm{Box}_X$ = `IntegerResidueBox loX (loX + NX) MX aX` nonempty, and likewise $\mathrm{lo}_Y, N_Y, M_Y, a_Y$ on $\tau$ with $\mathrm{Box}_Y$ nonempty. Let $q : \iota \to \mathbb{N}$ be nonzero and pairwise coprime. Let $K \subseteq \iota$, $\mathrm{base}_X \in \prod_i (\mathbb{Z}/q_i)^{\sigma}$, $\mathrm{base}_Y \in \prod_i (\mathbb{Z}/q_i)^{\tau}$, and let $u_X$, $u_Y$ be points of the cells `ResiduePrimeCoordinateCell loX NX MX aX q K baseX` and `ResiduePrimeCoordinateCell loY NY MY aY q K baseY`. For each $i$ let $\mathrm{kernel}_i$ assign to each $x \in (\mathbb{Z}/q_i)^{\sigma}$ probability weights on $(\mathbb{Z}/q_i)^{\tau}$, and let $C : \iota \to \mathbb{R}$ with $C_i \ge 0$. Assume, writing $\mathbb{E}_\sigma$ and $\mathbb{E}_\tau$ for uniform averages over $(\mathbb{Z}/q_i)^{\sigma}$ and $(\mathbb{Z}/q_i)^{\tau}$:
--   - for every $i$ and every $f : (\mathbb{Z}/q_i)^{\tau} \to \mathbb{R}$ with $\mathbb{E}_\tau f = 0$: $\mathbb{E}_{\sigma, x}\bigl(\mathbb{E}_{\mathrm{kernel}_i(x)} f\bigr)^2 \le C_i\,\mathbb{E}_\tau f^2$;
--   - for every $i$ and every $f$: $\mathbb{E}_{\sigma, x}\,\mathbb{E}_{\mathrm{kernel}_i(x)} f = \mathbb{E}_\tau f$.
--
--   Let $w : \mathbb{Z}^{\sigma} \to \mathbb{R}$, $f : \mathbb{Z}^{\tau} \to \mathbb{R}$, and $B \in \mathbb{N}$ with $|K| \le B$. Let $\kappa$, $\mathrm{sourceNorm}$, $\mathrm{siteNorm}$ be real numbers with $0 \le \kappa \le 1$ and $C_i \le \kappa^2$ for every $i \notin K$. Write $w^{\mathrm{out}}$ = `residueCellOutsideDensity loX NX MX aX q K baseX uX w` and $f^{\mathrm{out}}$ = `residueCellOutsideDensity loY NY MY aY q K baseY uY f`, functions on $\prod_{i \notin K}(\mathbb{Z}/q_i)^{\sigma}$ and $\prod_{i \notin K}(\mathbb{Z}/q_i)^{\tau}$. Assume
--   $$\sqrt{\texttt{productANOVAEnergy}\ \bigl(\text{uniform on } (\mathbb{Z}/q_i)^{\sigma},\ i \notin K\bigr)\ (\texttt{lowDegreeCoordinateSets}\ \{i \notin K\}\ B)\ w^{\mathrm{out}}} \le \mathrm{sourceNorm},$$
--   and the same with $\tau$ and $f^{\mathrm{out}}$ bounded by $\mathrm{siteNorm}$.
--
--   Let $c_i$ = `FiniteProbabilityCoupling.ofKernel` of the uniform distributions on $(\mathbb{Z}/q_i)^{\sigma}$ and $(\mathbb{Z}/q_i)^{\tau}$ with the kernel $\mathrm{kernel}_i$ (using the second assumption). Let $\rho_X$ = `residuePrimeCoordinateMassRatio loX NX MX aX q K baseX` and $\rho_Y$ = `residuePrimeCoordinateMassRatio loY NY MY aY q K baseY`. Then
--   $$\Bigl|\,\texttt{productAtomTruncatedPairing}\ c\ \mathcal{L}\ K\ \mathrm{base}_X\ \mathrm{base}_Y\ W\ F \;-\; \texttt{productCouplingAtomMass}\ c\ K\ \mathrm{base}_X\ \mathrm{base}_Y \cdot \rho_X\,\rho_Y\cdot \texttt{productTruncatedPairing}\ (c_i)_{i \notin K}\ \mathcal{L}'\ w^{\mathrm{out}}\ f^{\mathrm{out}}\Bigr|$$
--   $$\le 2^{|K|}\,\Bigl(\kappa^{B - |K|}\,(\rho_X\,\mathrm{sourceNorm})\,(\rho_Y\,\mathrm{siteNorm})\Bigr),$$
--   where $\mathcal{L}$ = `lowDegreeCoordinateSets ι B`, $\mathcal{L}'$ = `lowDegreeCoordinateSets {i ∉ K} (B - |K|)` (natural-number subtraction, also in the exponent of $\kappa$), $W$ = `residuePrimeCoordinateDensity loX NX MX aX hneX q w` and $F$ = `residuePrimeCoordinateDensity loY NY MY aY hneY q f`.
--
--   Lean: `OAI.Erdos3.residue_initial_conditioning_shell_s2`, which states OpenAI's `OAI.Erdos3.residue_initial_conditioning_shell` (in `lean/OAI/Combinatorics/Progressions/Lattices/AffineMaskedInitialShell.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B193`, `OAIE3v2B197` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AffineMaskedInitialShell.lean (declaration OAI.Erdos3.residue_initial_conditioning_shell)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B193
import Definitions.Def_OAIE3v2B197

section

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem residue_initial_conditioning_shell_s2 {ι σ τ : Type*}
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
    {κ sourceNorm siteNorm : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hcap : ∀ i ∉ K, C i ≤ κ ^ 2)
    (hsourceNorm : Real.sqrt (productANOVAEnergy
      (primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val))
      (lowDegreeCoordinateSets {i // i ∉ K} B) (residueCellOutsideDensity loX NX MX aX q K baseX uX w)) ≤ sourceNorm)
    (hsiteNorm : Real.sqrt (productANOVAEnergy
      (primeCoordinateReference (σ := τ) (fun i : {i // i ∉ K} => q i.val))
      (lowDegreeCoordinateSets {i // i ∉ K} B) (residueCellOutsideDensity loY NY MY aY q K baseY uY f)) ≤ siteNorm) :
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
        (residuePrimeCoordinateMassRatio loX NX MX aX q K baseX * sourceNorm) *
        (residuePrimeCoordinateMassRatio loY NY MY aY q K baseY * siteNorm)) := by
  sorry

end Erdos3

end

end OAI
end
