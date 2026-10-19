-- Prove2me | Theorems.Thm_OAI_Erdos3_retained_residue_marginals_of_lengths_s2
-- name    : OAI.Erdos3.retained_residue_marginals_of_lengths_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:34:58.523562+00:00
-- url     : https://prove2.me/theorems/11aafda1-0d36-4bf4-af69-ceee48da8907
-- title:
--   Long residue index lengths make the retained prime-coordinate residue marginals close to uniform
-- statement:
--   Let $\iota$ and $\sigma$ be finite types with decidable equality. Let $\mathrm{lo} : \sigma \to \mathbb{Z}$, $N : \sigma \to \mathbb{N}$, $M > 0$ a natural number, $a : \sigma \to \mathbb{Z}$, and $q : \iota \to \mathbb{N}$ with every $q(i) \ne 0$ and the $q(i)$ pairwise coprime. Let $K \subseteq \iota$ be a finite set and $\mathrm{base}(i) : \sigma \to \mathbb{Z}/q(i)$ for each $i$, and assume $M$ is coprime to $q(i)$ for every $i \notin K$. Let $u$ be an element of `ResiduePrimeCoordinateCell lo N M a q K base` (OpenAI: a point $z$ of the box $\prod_k [\mathrm{lo}(k), \mathrm{lo}(k) + N(k))$ with every coordinate $z_k \equiv a(k) \pmod M$, such that $z \bmod q(i) = \mathrm{base}(i)$ for every $i \in K$). Let $R$ be a natural number and $B, C, D, \eta$ reals with $B \ge 0$, $\eta \le 1$, $e^{-D} \le \eta$, $q(i) \le e^B$ for every $i \notin K$, $\lvert\sigma\rvert \le e^C$, and for every $k \in \sigma$
--   $$e^{BR + D + C + 1} \le \ell_k := \texttt{residueIndexLength}\bigl(\mathrm{lo}(k),\ \mathrm{lo}(k) + N(k),\ \operatorname{lcm}(M, \textstyle\prod_{i \in K} q(i)),\ u_k\bigr)$$
--   (the number of integers in $[\mathrm{lo}(k), \mathrm{lo}(k) + N(k))$ congruent to $u_k$ modulo the given modulus).
--
--   Then:
--   1. `ProductMarginalsClose μ ρ η R` holds, where $\mu$ = `primeCoordinateReference` is the family of uniform laws on $(\mathbb{Z}/q(i))^\sigma$ for $i \notin K$, and $\rho$ = `residuePrimeCoordinateDensity lo N (lcm M ∏_{i∈K} q i) u … (q restricted to i ∉ K) (fun _ => 1)` is OpenAI's density, relative to $\mu$, of the joint residues modulo the $q(i)$ ($i \notin K$) of a uniform point of the residue box $\{z \in \prod_k [\mathrm{lo}(k), \mathrm{lo}(k)+N(k)) : z_k \equiv u_k \bmod \operatorname{lcm}(M, \prod_{i\in K} q(i))\}$. By OpenAI's definition this means: for every set $S'$ of at most $R$ indices outside $K$ and every $x$ of positive product weight, the conditional mean of $\rho$ given the coordinates in $S'$ (`productConditionalMean`) is within $\eta$ of $1$.
--   2. For every finite set $S$ of indices outside $K$ with $\lvert S\rvert \le R$,
--   $$2\sum_{k \in \sigma} \frac{\prod_{i \in S} q(i)}{\ell_k} \le \eta.$$
--
--   Lean: `OAI.Erdos3.retained_residue_marginals_of_lengths_s2`, which states OpenAI's `OAI.Erdos3.retained_residue_marginals_of_lengths` (in `lean/OAI/Combinatorics/Progressions/Lattices/ResidueCellNormLengths.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B193` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/ResidueCellNormLengths.lean (declaration OAI.Erdos3.retained_residue_marginals_of_lengths)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B193

section

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem retained_residue_marginals_of_lengths_s2 {ι σ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ)
    [∀ i, NeZero (q i)] (hM : 0 < M) (hpair : Pairwise (fun i k => (q i).Coprime (q k)))
    (K : Finset ι) (base : ∀ i, σ → ZMod (q i)) (hcop : ∀ i ∉ K, M.Coprime (q i))
    (u : ResiduePrimeCoordinateCell lo N M a q K base)
    (R : ℕ) (B C D η : ℝ) (hB : 0 ≤ B) (hη : η ≤ 1) (herror : Real.exp (-D) ≤ η)
    (hmoduli : ∀ i ∉ K, (q i : ℝ) ≤ Real.exp B)
    (hdim : (Fintype.card σ : ℝ) ≤ Real.exp C)
    (hlength : ∀ k, Real.exp (B * R + D + C + 1) ≤
      (residueIndexLength (lo k) (lo k + N k) (M.lcm (∏ i ∈ K, q i)) ((u.val k).val) : ℝ)) :
    ProductMarginalsClose (primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val))
      (residuePrimeCoordinateDensity lo N (M.lcm (∏ i ∈ K, q i)) (fun k => (u.val k).val)
        (residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u)
        (fun i : {i // i ∉ K} => q i.val) (fun _ => 1)) η R ∧
    ∀ S : Finset {i // i ∉ K}, S.card ≤ R →
      2 * (∑ k, ((∏ i ∈ S, q i.val : ℕ) : ℝ) /
        residueIndexLength (lo k) (lo k + N k) (M.lcm (∏ i ∈ K, q i)) ((u.val k).val)) ≤ η := by
  sorry

end Erdos3

end

end OAI
end
