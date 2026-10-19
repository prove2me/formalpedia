-- Prove2me | Theorems.Thm_OAI_Erdos3_residue_source_stable_affine_comparison_at_degree_s2
-- name    : OAI.Erdos3.residue_source_stable_affine_comparison_at_degree_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:34:55.46883+00:00
-- url     : https://prove2.me/theorems/4b355a8e-ff88-470d-8887-1d9369d2bcb6
-- title:
--   Truncated affine residue pairing bound for a stable prime-coordinate refinement at a given degree
-- statement:
--   Let $\iota$ be a finite linearly ordered type, and $\sigma$ and $J$ finite types. Let $h, g : \mathbb{Z}^\sigma \to \mathbb{C}$, $\mathrm{lo}, a \in \mathbb{Z}^\sigma$, $N : \sigma \to \mathbb{N}$, $M$ a natural number, and $q : \iota \to \mathbb{N}$ with every $q_i \ne 0$. Let $\varepsilon, L, T, C, \mathrm{shell}, \mathrm{modLog}, \mathrm{level}$ be reals, $K$ a finite subset of $\iota$, $\mathrm{base}_i \in (\mathbb{Z}/q_i)^\sigma$ for each $i$, and $b$ a natural number. Write $r = \texttt{affineRemovalDepth}\ T + \texttt{affineComparisonTail}\ \varepsilon\ L\ T$ and $P$ = `affineComparisonScale ε L T C` (explicit natural-number, respectively real, functions of OpenAI). For a finite set $I' \subseteq \iota$ and residues $x$, a cell `ResiduePrimeCoordinateCell lo N M a q I' x` is the set of points $z$ of the residue box (points with $\mathrm{lo}_k \le z_k < \mathrm{lo}_k + N_k$ and $z_k \equiv a_k \pmod M$ for all $k$; OpenAI's `IntegerResidueBox`) whose reductions modulo $q_i$ equal $x_i$ for all $i \in I'$.
--
--   Assume:
--   - (hb) `affineComparisonDegree |Option J × σ| |σ| ε L T C shell modLog` $\le b$ (an explicit natural number of OpenAI);
--   - (hstable) `ResiduePrimeCoordinateStable g lo N M a q r (affineStabilityTolerance T) K base`: for every finite $J' \subseteq \iota$ disjoint from $K$ with $|J'| \le r$ and all residues $y$ agreeing with `base` on $K$ such that the cell for $K \cup J'$ and $y$ is nonempty, the mean of $g$ over the cell for $K$ and `base` and its mean over the cell for $K \cup J'$ and $y$ differ in norm by at most `affineStabilityTolerance T`;
--   - (hupper) `PrimeRefinementUpperBound h g lo N M a q r level (affineIncrementTolerance L T) (affineStabilityTolerance T) K base`: for the same $J'$ and $y$, $\operatorname{Re}(\text{mean of } h \text{ over the cell for } K \cup J', y) \le \mathrm{level} \cdot \operatorname{Re}(\text{mean of } g \text{ over the cell for } K, \mathrm{base}) + \texttt{affineIncrementTolerance L T} + \mathrm{level} \cdot \texttt{affineStabilityTolerance T}$;
--   - $M > 0$; the $q_i$ are pairwise coprime; $M$ is coprime to $q_i$ for all $i \notin K$;
--   - $u$ is an element of the cell `ResiduePrimeCoordinateCell lo N M a q K base`;
--   - $0 \le \operatorname{Re} g(z) \le 1$ and $0 \le \operatorname{Re} h(z) \le 1$ for all $z$ in the box $\prod_k [\mathrm{lo}_k, \mathrm{lo}_k + N_k)$ (`translatedIntegerBox lo N`);
--   - $L \ge 0$, $T \ge 0$, $e^{-L} \le \mathrm{level} \le 2$;
--   - $\mathrm{prime}, \mathrm{power} : \iota \to \mathbb{N}$ with every $\mathrm{prime}_i$ prime and $q_i = \mathrm{prime}_i^{\mathrm{power}_i}$;
--   - $|J| \ge 2$; $\mathrm{shell} > 0$; $\mathrm{modLog} \ge 0$; $q_i \le e^{\mathrm{modLog}}$ for $i \notin K$; $\varepsilon > 0$; $C \ge 0$; $|\iota| \le e^C$;
--   - (hmandatory) `affineMandatoryPrimes prime (ε / (2 + ε)) P` $\subseteq K$ (the set of $i$ with $\mathrm{prime}_i$ at most OpenAI's threshold `affineComparisonPrimeThreshold (ε/(2+ε)) P`);
--   - a real $\mathrm{dimLog}$ with $|\sigma| \le e^{\mathrm{dimLog}}$, and (hlength) for every $k \in \sigma$,
--   $$\exp\bigl(\mathrm{modLog} \cdot \max\bigl(r\,(\texttt{affineComparisonMoment}\ P + 1),\ 2b + \texttt{affineRemovalDepth}\ T\bigr) + \texttt{affineComparisonAccuracyLog b P L T} + \mathrm{dimLog} + 1\bigr) \le \texttt{residueIndexLength}(\mathrm{lo}_k, \mathrm{lo}_k + N_k, \operatorname{lcm}(M, \textstyle\prod_{i \in K} q_i), u_k),$$
--   where `affineComparisonMoment P` $= 2(\lfloor P/2 \rfloor + 1)$, `affineComparisonAccuracyLog` is an explicit real function of OpenAI, and `residueIndexLength lo hi r v` is the number of integers in $[\mathrm{lo}, \mathrm{hi})$ congruent to $v$ modulo $r$ (as defined by OpenAI);
--   - source data: $\mathrm{sourceLo}, \mathrm{sourceA} : \mathrm{Option}\ J \times \sigma \to \mathbb{Z}$, $\mathrm{sourceN} : \mathrm{Option}\ J \times \sigma \to \mathbb{N}$ and a natural number $\mathrm{sourceM} > 0$ coprime to $q_i$ for all $i \notin K$, such that the source residue box (points $z$ with $\mathrm{sourceLo}_k \le z_k < \mathrm{sourceLo}_k + \mathrm{sourceN}_k$ and $z_k \equiv \mathrm{sourceA}_k \pmod{\mathrm{sourceM}}$) is nonempty; a weight $w$ on $\mathbb{Z}^{\mathrm{Option} J \times \sigma}$ with $0 \le w(z) \le 1$ on that box; a real $\mathrm{sourceDimLog}$ with $|\mathrm{Option}\ J \times \sigma| \le e^{\mathrm{sourceDimLog}}$; and (hsourceLength) for every $k$, the same exponential as in (hlength) with $\mathrm{dimLog}$ replaced by $\mathrm{sourceDimLog}$ is at most `residueIndexLength (sourceLo k) (sourceLo k + sourceN k) sourceM (sourceA k)`.
--
--   Let `density f` = `residuePrimeCoordinateDensity lo N (lcm(M, ∏_{i∈K} q_i)) (u) _ (q restricted to the complement of K) f`, OpenAI's density, on residues $(\mathbb{Z}/q_i)^\sigma$ for $i \notin K$, of the observed residues of the uniform point of the residue box with modulus $\operatorname{lcm}(M, \prod_{i \in K} q_i)$ and residue $u$, weighted by $f$; and let $\omega$ be the analogous `residuePrimeCoordinateDensity` of the source box weighted by $w$. Then
--   $$\texttt{affineResidueTruncatedPairing}\Bigl(q|_{\iota \setminus K},\ \texttt{lowDegreeCoordinateSets b},\ \omega,\ z \mapsto \texttt{density}(\operatorname{Re} h)(z) - (1 + \varepsilon)\,\mathrm{level} \cdot \texttt{density}(\operatorname{Re} g)(z)\Bigr)$$
--   is at most
--   $$\mathrm{level}\,(1 + 2\varepsilon)\, e^{-T} + \frac{\mathrm{shell}}{16} + \sqrt{3 e^{-T}}\,\bigl(3 + 3(1 + \varepsilon)\,\mathrm{level}\bigr),$$
--   where `lowDegreeCoordinateSets b` is the family of subsets of $\iota \setminus K$ of size at most $b$, and `affineResidueTruncatedPairing` is OpenAI's truncated pairing of a source density with a target density through the affine sample product coupling, applied after truncating both densities to their ANOVA components indexed by that family (`productANOVATruncation`).
--
--   Lean: `OAI.Erdos3.residue_source_stable_affine_comparison_at_degree_s2`, which states OpenAI's `OAI.Erdos3.residue_source_stable_affine_comparison_at_degree` (in `lean/OAI/Combinatorics/Progressions/Polynomial/InitialMaskedAffineComparisonAtDegree.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B193`, `OAIE3v2B197` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Polynomial/InitialMaskedAffineComparisonAtDegree.lean (declaration OAI.Erdos3.residue_source_stable_affine_comparison_at_degree)

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

variable {ι σ J : Type*} [Fintype J] [Fintype ι] [LinearOrder ι] [Fintype σ]
variable {h g : (σ → ℤ) → ℂ} {lo a : σ → ℤ} {N : σ → ℕ} {M : ℕ} {q : ι → ℕ}
variable [∀ i, NeZero (q i)]
variable {ε L T C shell modLog level : ℝ} {K : Finset ι} {base : ∀ i, σ → ZMod (q i)}
variable {b : ℕ}
variable (hb : affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog ≤ b)

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

variable (sourceLo sourceA : Option J × σ → ℤ) (sourceN : Option J × σ → ℕ) (sourceM : ℕ)
variable (sourceNonempty : Nonempty (IntegerResidueBox sourceLo
  (fun k => sourceLo k + sourceN k) (fun _ => (sourceM : ℤ)) sourceA))
variable (w : (Option J × σ → ℤ) → ℝ)
variable (hw : ∀ z : IntegerResidueBox sourceLo (fun k => sourceLo k + sourceN k)
    (fun _ => (sourceM : ℤ)) sourceA,
  0 ≤ w (fun k => (z k).val) ∧ w (fun k => (z k).val) ≤ 1)
variable (hsourceM : 0 < sourceM)
variable (hsourceCop : ∀ i ∉ K, sourceM.Coprime (q i))
variable (sourceDimLog : ℝ)
variable (hsourceDim : (Fintype.card (Option J × σ) : ℝ) ≤ Real.exp sourceDimLog)
variable (hsourceLength : ∀ k, Real.exp (modLog *
    (max ((affineRemovalDepth T + affineComparisonTail ε L T) *
      (affineComparisonMoment (affineComparisonScale ε L T C) + 1))
      (2 * b + affineRemovalDepth T) : ℕ) +
    affineComparisonAccuracyLog
      (b)
      (affineComparisonScale ε L T C) L T + sourceDimLog + 1) ≤
    (residueIndexLength (sourceLo k) (sourceLo k + sourceN k) sourceM (sourceA k) : ℝ))

include hb hstable hupper hM hpair hcop u hg hh hL hT hlower prime power hprime hpower hJ hshell hlevel2 hmodLog hmoduli hε hC hcount hmandatory dimLog hdim hlength sourceLo sourceA sourceN sourceM sourceNonempty w hw hsourceM hsourceCop sourceDimLog hsourceDim hsourceLength

theorem residue_source_stable_affine_comparison_at_degree_s2 :
    let density := fun f => residuePrimeCoordinateDensity lo N (M.lcm (∏ i ∈ K, q i))
      (fun k => (u.val k).val) (residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u)
      (fun i : {i // i ∉ K} => q i.val) f
    affineResidueTruncatedPairing (J := J) (σ := σ) (fun i : {i // i ∉ K} => q i.val)
      (lowDegreeCoordinateSets {i // i ∉ K} (b)) (residuePrimeCoordinateDensity sourceLo sourceN sourceM sourceA sourceNonempty
        (fun i : {i // i ∉ K} => q i.val) w)
      (fun z => density (fun x => (h x).re) z - (1 + ε) * level * density (fun x => (g x).re) z) ≤
      level * (1 + 2 * ε) * (Real.exp (-T)) + shell / 16 + Real.sqrt (3 * (Real.exp (-T))) * (3 + (1 + ε) * level * 3) := by
  sorry

end

end Erdos3

end

end OAI
end
