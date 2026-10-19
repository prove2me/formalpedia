-- Prove2me | Theorems.Thm_OAI_Erdos3_stable_residue_kernel_total_s2
-- name    : OAI.Erdos3.stable_residue_kernel_total_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:35:31.650155+00:00
-- url     : https://prove2.me/theorems/d67ee988-349a-4350-b6e4-5dc49ecdc529
-- title:
--   Truncated coupling pairing bound for a stable residue cell after cylinder removal, via a contracting coordinate kernel
-- statement:
--   All objects named in backticks are defined by OpenAI; hypothesis names in parentheses are those of the Lean statement.
--
--   **Setting.** Let $\Omega$ be a finite type, $\iota$ a finite linearly ordered type, and $\sigma$ a finite type with decidable equality. Let $h, g : \mathbb{Z}^\sigma \to \mathbb{C}$, $\mathrm{lo}, a : \sigma \to \mathbb{Z}$, $N : \sigma \to \mathbb{N}$, $M$ a natural number, and $q : \iota \to \mathbb{N}$ with every $q(i) \ne 0$. Let $j, r, b, \mathrm{moment}$ be natural numbers, $\mathrm{level}, \mathrm{inc}, \delta, \eta, \tau, L, T, P$ reals, $K \subseteq \iota$ a finite set, and $\mathrm{base}(i) : \sigma \to \mathbb{Z}/q(i)$ for each $i$. Write $\iota' = \{i \in \iota : i \notin K\}$. For $i \in \iota'$ let $X_i$ be a finite type with decidable equality and $\mu_i$ probability weights on $X_i$; let $p$ be probability weights on $\Omega$, $F : \Omega \to \prod_{i \in \iota'} X_i$, $\mathrm{sourceBase} \in \prod_i X_i$, and $\mathrm{siteBase}(i) : \sigma \to \mathbb{Z}/q(i)$ for $i \in \iota'$ (this last datum appears nowhere else). Let $\mathrm{reg}_K, \kappa, \varepsilon, \xi, \mathrm{shell}, Q$ be reals, $w, \mathrm{rem} : \Omega \to \mathbb{R}$, and $\mathrm{cs}$ a list of product cylinders (pairs of a finite set $S \subseteq \iota'$ and a point of $\prod_{i \in S} X_i$). Let $\mathcal{B} = \mathrm{lo} + \prod_k [0, N(k))$ = `translatedIntegerBox lo N`, and write $\mathrm{mean}_I(f, x)$ = `residuePrimeCoordinateMean f lo N M a q I x` for the average of $f$ over the cell `ResiduePrimeCoordinateCell lo N M a q I x` of points $z$ of the residue box (`IntegerResidueBox lo (lo + N) M a`) with $z \equiv x(i) \pmod{q(i)}$ coordinatewise for all $i \in I$.
--
--   **Hypotheses.**
--   - (hchain) `CylinderRemovalChain μ sourceBase p F regK τ j r w rem cs`: removing the cylinders of `cs` one at a time from the weight $w$ (each of size at most $j$, of observed mass more than $\tau$, with normalized section having `ProductBoundedMarginals` with constant $\mathrm{reg}_K$ up to order $r$) leaves the weight $\mathrm{rem}$;
--   - $\mu_i(x) > 0$ for all $i, x$; $\mathrm{reg}_K \ge 1$; $0 \le w \le 1$ and $0 \le \mathrm{rem} \le 1$ pointwise; $\mathbb{E}_p\, \mathrm{rem} \le \tau$;
--   - (hstable) `ResiduePrimeCoordinateStable g lo N M a q (j + r) δ K base`: for every $J \subseteq \iota$ disjoint from $K$ with $\#J \le j + r$ and every $y$ agreeing with $\mathrm{base}$ on $K$ whose cell for $K \cup J$ is nonempty, $\|\mathrm{mean}_K(g, \mathrm{base}) - \mathrm{mean}_{K \cup J}(g, y)\| \le \delta$;
--   - (hupper) `PrimeRefinementUpperBound h g lo N M a q (j + r) level inc δ K base`: for the same $J, y$, $\operatorname{Re} \mathrm{mean}_{K \cup J}(h, y) \le \mathrm{level} \cdot \operatorname{Re}\mathrm{mean}_K(g, \mathrm{base}) + \mathrm{inc} + \mathrm{level}\cdot\delta$;
--   - $M > 0$; the $q(i)$ are pairwise coprime; $M$ is coprime to $q(i)$ for $i \notin K$; $u$ is an element of the cell `ResiduePrimeCoordinateCell lo N M a q K base`;
--   - $\operatorname{Re} g$ and $\operatorname{Re} h$ take values in $[0,1]$ on $\mathcal{B}$;
--   - $\mathrm{level} > 0$, $\tau > 0$, $\delta \le \tau/8$, $\mathrm{inc} \le \mathrm{level}\,\tau/8$, $0 \le \eta < 1$, $\eta \le \tau/8$, $\eta \le \mathrm{level}\,\tau/8$, $L \ge 0$, $T \ge 0$, $e^{-L} \le \mathrm{level}$, $\tau^{-1} \le e^T$, $L + T + 2 \le P$, $j + r \le P$;
--   - $\mathrm{moment} \ge 2$ is even with $P \le \mathrm{moment} \le P + 2$; $\#\iota \le e^P$; $\eta \le \frac12 e^{-(P+3)^3}$;
--   - (herror) for every $S \subseteq \iota'$ with $\#S \le j + r$: $2 \sum_{k \in \sigma} \bigl(\prod_{i \in S} q(i)\bigr) / \texttt{residueIndexLength}(\mathrm{lo}(k), \mathrm{lo}(k) + N(k), M', u_k) \le \eta$, where $M' = \operatorname{lcm}(M, \prod_{i \in K} q(i))$ and $u_k$ the $k$-th coordinate of $u$ (OpenAI's `residueIndexLength`, the number of residue indices of the progression $u_k + M'\mathbb{Z}$ between $\mathrm{lo}(k)$ and $\mathrm{lo}(k) + N(k)$);
--   - (hclose) with $\nu_i$ = `primeCoordinateReference q i` the uniform weights on $\sigma \to \mathbb{Z}/q(i)$ for $i \in \iota'$, and $\varrho_f$ = `residuePrimeCoordinateDensity lo N M' u (q on ι') f` (the observed density, relative to $\prod_i \nu_i$, of the residues modulo the $q(i)$ of a uniform point of the residue box with modulus $M'$ and residue $u$, weighted by $f$): `ProductMarginalsClose ν ϱ₁ η (max ((j + r)(moment + 1)) (2b + j))` (all conditional means of $\varrho_1$ over at most that many coordinates are within $\eta$ of $1$);
--   - (hgram) $2\eta \cdot (\#\mathcal{D})^2 \cdot 4^b (1+\eta)^2 \le 1$, where $\mathcal{D}$ = `lowDegreeCoordinateSets ι' b` is the family of subsets of $\iota'$ of size at most $b$;
--   - (hsourceclose) `ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η (max ((j + r)(moment + 1)) (2b + j))`;
--   - (hresGram) $2\eta \cdot (\#\mathcal{D})^2 \cdot 4^b (1+\eta)^2 \le \tau$;
--   - $\mathrm{kernel}_i : X_i \to$ probability weights on $\sigma \to \mathbb{Z}/q(i)$ for $i \in \iota'$, and $C : \iota' \to \mathbb{R}$ with $C_i \ge 0$, such that for every $f$ with $\mathbb{E}_{\nu_i} f = 0$, $\mathbb{E}_{x \sim \mu_i} (\mathbb{E}_{\mathrm{kernel}_i(x)} f)^2 \le C_i\, \mathbb{E}_{\nu_i} f^2$ (hbound), and for every $f$, $\mathbb{E}_{x \sim \mu_i} \mathbb{E}_{\mathrm{kernel}_i(x)} f = \mathbb{E}_{\nu_i} f$ (hK);
--   - $\varepsilon \ge 0$, $0 < \xi \le 1$, $\xi(2 + \varepsilon) \le \varepsilon$, $0 \le \kappa \le 1/2$, $C_i \le \kappa^2$ for all $i$, and $\kappa (8(1 + \mathrm{reg}_K)(P+2))^2 (16(P+2))^2 \le \xi/16$;
--   - $\mathrm{SI}(\xi, L + 2T + 4) \le r$, $j + r \le b$, $\mathrm{shell} > 0$, and $j + \mathrm{SI}(\mathrm{shell}, Q) \le b$, where $\mathrm{SI}(\epsilon, x)$ = `CyclicCrootSisask.spectralIterations` $= \lceil (x + \log(16/\epsilon))/\log 2 \rceil + 1$;
--   - (hbudget) summing over the cylinders $c = (S, \cdot)$ of `cs` paired with their removed weights $w_c$ (`removedCylinderWeights F w cs`), $\sum_c \#(\prod_{i \in S} (\sigma \to \mathbb{Z}/q(i))) \cdot m_c \cdot \mathrm{level} \cdot (\operatorname{Re} \mathrm{mean}_K(g, \mathrm{base}) + \tau) (6 + 2\varepsilon)\, 2^{\#S} (3\tau^{-1})(3 e^{L+T}) \le e^Q$, where $m_c$ is the cylinder mass `c.mass μ sourceBase (observedProductDensity μ p F w_c)`.
--
--   **Conclusion.** Let $\gamma_i$ = `FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (kernel i) (hK i)` (the coupling of $\mu_i$ and $\nu_i$ given by drawing $x \sim \mu_i$ and then $y \sim \mathrm{kernel}_i(x)$). Then
--   $$\texttt{productTruncatedPairing}\ \gamma\ \mathcal{D}\ \bigl(\texttt{observedProductDensity μ p F w}\bigr)\ \bigl(z \mapsto \varrho_{\operatorname{Re} h}(z) - (1+\varepsilon)\,\mathrm{level}\, \varrho_{\operatorname{Re} g}(z)\bigr) \le \mathrm{level}(1 + 2\varepsilon)\tau + \frac{\mathrm{shell}}{16} + \sqrt{3\tau}\,\bigl(3 + 3(1+\varepsilon)\,\mathrm{level}\bigr),$$
--   where `productTruncatedPairing` pairs, through the product coupling $\gamma$, the ANOVA truncations to the coordinate sets $\mathcal{D}$ of the two functions (relative to $\prod \mu_i$ and $\prod \nu_i$ respectively).
--
--   Lean: `OAI.Erdos3.stable_residue_kernel_total_s2`, which states OpenAI's `OAI.Erdos3.stable_residue_kernel_total` (in `lean/OAI/Combinatorics/Progressions/Lattices/StableResidueKernelTotal.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B193` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/StableResidueKernelTotal.lean (declaration OAI.Erdos3.stable_residue_kernel_total)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B193

section

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem stable_residue_kernel_total_s2 {Ω ι σ : Type*}
    [Fintype Ω]
    [Fintype ι] [LinearOrder ι] [Fintype σ] [DecidableEq σ]
    {h g : (σ → ℤ) → ℂ} {lo a : σ → ℤ} {N : σ → ℕ} {M : ℕ} {q : ι → ℕ}
    [∀ i, NeZero (q i)] {j r b moment : ℕ} {level inc δ η τ L T P : ℝ} {K : Finset ι}
    {base : ∀ i, σ → ZMod (q i)}
    {X : {i // i ∉ K} → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (p : FiniteProbabilityWeights Ω)
    (F : Ω → ∀ i, X i) (sourceBase : ∀ i, X i)
    (siteBase : ∀ i : {i // i ∉ K}, σ → ZMod (q i.val))
    {regK κ ε ξ shell Q : ℝ} {w rem : Ω → ℝ} {cs : List (ProductCylinder X)}
    (hchain : CylinderRemovalChain μ sourceBase p F regK τ j r w rem cs)
    (hμ : ∀ i x, 0 < (μ i).weight x) (hregK : 1 ≤ regK)
    (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1) (hrem : ∀ z, 0 ≤ rem z ∧ rem z ≤ 1) (hmass : p.mean rem ≤ τ)
    (hstable : ResiduePrimeCoordinateStable g lo N M a q (j + r) δ K base)
    (hupper : PrimeRefinementUpperBound h g lo N M a q (j + r) level inc δ K base)
    (hM : 0 < M) (hpair : Pairwise (fun i k => (q i).Coprime (q k)))
    (hcop : ∀ i ∉ K, M.Coprime (q i)) (u : ResiduePrimeCoordinateCell lo N M a q K base)
    (hg : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (g z).re ∧ (g z).re ≤ 1)
    (hh : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1)
    (hlevel : 0 < level) (hτ : 0 < τ) (hδ : δ ≤ τ / 8) (hinc : inc ≤ level * τ / 8)
    (hη0 : 0 ≤ η) (hη : η < 1) (hητ : η ≤ τ / 8) (hηlevel : η ≤ level * τ / 8)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hlower : Real.exp (-L) ≤ level) (hτinv : τ⁻¹ ≤ Real.exp T)
    (hlog : L + T + 2 ≤ P) (hrP : ((j + r : ℕ) : ℝ) ≤ P)
    (hmoment : 2 ≤ moment) (heven : Even moment) (hPq : P ≤ (moment : ℝ)) (hqP : (moment : ℝ) ≤ P + 2)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P)
    (hηsmall : η ≤ (1 / 2) * Real.exp (-((P + 3) ^ 3)))
    (herror : ∀ S : Finset {i // i ∉ K}, S.card ≤ j + r →
      2 * (∑ k, ((∏ i ∈ S, q i.val : ℕ) : ℝ) /
        residueIndexLength (lo k) (lo k + N k) (M.lcm (∏ i ∈ K, q i)) ((u.val k).val)) ≤ η)
    (hclose : ProductMarginalsClose (primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val))
      (residuePrimeCoordinateDensity lo N (M.lcm (∏ i ∈ K, q i)) (fun k => (u.val k).val)
        (residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u)
        (fun i : {i // i ∉ K} => q i.val) (fun _ => 1)) η
      (max ((j + r) * (moment + 1)) (2 * b + j)))
    (hgram : 2 * η * ((lowDegreeCoordinateSets {i // i ∉ K} b).card : ℝ) ^ 2 *
      (4 : ℝ) ^ b * (1 + η) ^ 2 ≤ 1)
    (hsourceclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η
      (max ((j + r) * (moment + 1)) (2 * b + j)))
    (hresGram : 2 * η * ((lowDegreeCoordinateSets {i // i ∉ K} b).card : ℝ) ^ 2 *
      (4 : ℝ) ^ b * (1 + η) ^ 2 ≤ τ)
    (kernel : ∀ i : {i // i ∉ K}, X i → FiniteProbabilityWeights (σ → ZMod (q i.val)))
    (C : {i // i ∉ K} → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i : {i // i ∉ K}, ∀ f : (σ → ZMod (q i.val)) → ℝ,
      (primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val) i).mean f = 0 →
      (μ i).mean (fun x => (kernel i x).mean f ^ 2) ≤ C i *
        (primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val) i).mean (fun y => f y ^ 2))
    (hK : ∀ i : {i // i ∉ K}, ∀ f : (σ → ZMod (q i.val)) → ℝ, (μ i).mean (fun x => (kernel i x).mean f) =
      (primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val) i).mean f)
    (hε : 0 ≤ ε) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hslack : ξ * (2 + ε) ≤ ε)
    (hκ0 : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2) (hcap : ∀ i, C i ≤ κ ^ 2)
    (hlow : κ * (8 * (1 + regK) * (P + 2)) ^ 2 * (16 * (P + 2)) ^ 2 ≤ ξ / 16)
    (hrtail : CyclicCrootSisask.spectralIterations ξ (L + 2 * T + 4) ≤ r) (hrb : j + r ≤ b)
    (hshell : 0 < shell) (hb : j + CyclicCrootSisask.spectralIterations shell Q ≤ b)
    (hbudget : ((cs.zip (removedCylinderWeights F w cs)).map (fun cf =>
      (Fintype.card (∀ i : cf.1.1, σ → ZMod (q i.val.val)) : ℝ) *
        (cf.1.mass μ sourceBase (observedProductDensity μ p F cf.2) * level *
          ((residuePrimeCoordinateMean g lo N M a q K base).re + τ) * (6 + 2 * ε) *
          (2 : ℝ) ^ cf.1.1.card * (3 * τ⁻¹) * (3 * Real.exp (L + T))))).sum ≤ Real.exp Q) :
    let density := fun f => residuePrimeCoordinateDensity lo N (M.lcm (∏ i ∈ K, q i))
      (fun k => (u.val k).val) (residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u)
      (fun i : {i // i ∉ K} => q i.val) f
    let ν := primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val)
    let c := fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (kernel i) (hK i)
    productTruncatedPairing c (lowDegreeCoordinateSets {i // i ∉ K} b) (observedProductDensity μ p F w)
      (fun z => density (fun x => (h x).re) z - (1 + ε) * level * density (fun x => (g x).re) z) ≤
      level * (1 + 2 * ε) * τ + shell / 16 + Real.sqrt (3 * τ) * (3 + (1 + ε) * level * 3) := by
  sorry

end Erdos3

end

end OAI
end
