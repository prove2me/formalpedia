-- Prove2me | Theorems.Thm_OAI_Erdos3_stable_site_normalized_marginals_s2
-- name    : OAI.Erdos3.stable_site_normalized_marginals_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:51:38.01899+00:00
-- url     : https://prove2.me/theorems/d18c8e73-68f4-4375-b0ab-12a0cfda99ba
-- title:
--   Bounded normalized prime-coordinate marginals at a stable site under a prime refinement upper bound
-- statement:
--   Let $\iota$ and $\sigma$ be finite types with decidable equality. Let $h, g : \mathbb{Z}^\sigma \to \mathbb{C}$, $\mathrm{lo}, a : \sigma \to \mathbb{Z}$, $N : \sigma \to \mathbb{N}$, $M$ a natural number, $q : \iota \to \mathbb{N}$ with every $q(i) \ne 0$, $r$ a natural number, $\mathrm{level}, \varepsilon, \delta, \eta, \tau$ reals, $K \subseteq \iota$ a finite set and $\mathrm{base}(i) : \sigma \to \mathbb{Z}/q(i)$. For $I \subseteq \iota$ and $x$, `residuePrimeCoordinateMean f lo N M a q I x` denotes OpenAI's average of $f$ over the cell `ResiduePrimeCoordinateCell lo N M a q I x` (points $z$ of the box $\prod_j [\mathrm{lo}(j), \mathrm{lo}(j) + N(j))$ with $z_j \equiv a(j) \pmod M$ and $z \bmod q(i) = x(i)$ for $i \in I$). Assume:
--   - `ResiduePrimeCoordinateStable g lo N M a q r δ K base` (OpenAI: for every set $J$ disjoint from $K$ with $\lvert J\rvert \le r$ and every $y$ agreeing with $\mathrm{base}$ on $K$ whose cell for $K \cup J$ is nonempty, the mean of $g$ over that cell differs from the mean of $g$ over the cell for $(K, \mathrm{base})$ by at most $\delta$ in norm);
--   - `PrimeRefinementUpperBound h g lo N M a q r level ε δ K base` (OpenAI: for the same $J$ and $y$, the real part of the mean of $h$ over the $(K \cup J, y)$ cell is at most $\mathrm{level}$ times the real part of the mean of $g$ over the $(K, \mathrm{base})$ cell, plus $\varepsilon + \mathrm{level}\cdot\delta$);
--   - $M > 0$, the $q(i)$ pairwise coprime, and $M$ coprime to $q(i)$ for every $i \notin K$;
--   - $u$ is an element of `ResiduePrimeCoordinateCell lo N M a q K base`;
--   - $0 \le \operatorname{Re} g(z) \le 1$ and $\lvert\operatorname{Re} h(z)\rvert \le 1$ for every $z$ in the box `translatedIntegerBox lo N`;
--   - $\mathrm{level} > 0$, $\tau > 0$, $\delta \le \tau$, $\varepsilon \le \mathrm{level}\cdot\tau$, $\eta < 1$, $\eta \le \tau$, $\eta \le \mathrm{level}\cdot\tau$;
--   - for every set $S$ of indices outside $K$ with $\lvert S\rvert \le r$: $2\sum_{j \in \sigma} \bigl(\prod_{i \in S} q(i)\bigr)/\ell_j \le \eta$, where $\ell_j$ = `residueIndexLength (lo j) (lo j + N j) (lcm M ∏_{i∈K} q i) u_j`.
--
--   Let $v$ be the real part of `residuePrimeCoordinateMean g lo N M a q K base`, let $\mu$ = `primeCoordinateReference` (the uniform laws on $(\mathbb{Z}/q(i))^\sigma$ for $i \notin K$), and for a real function $f$ and a real scale let $\mathrm{density}(f, \mathrm{scale})$ = `normalizedResiduePrimeDensity lo N (lcm M ∏_{i∈K} q i) u … (q restricted to i ∉ K) f scale` (OpenAI: $\mathrm{scale}^{-1}$ times the density relative to $\mu$ of the joint residues, weighted by $f$, of a uniform point of the residue box of $u$). Then both
--   - `ProductBoundedMarginals μ (density (Re ∘ g) (2(v + τ))) 1 r`, and
--   - `ProductBoundedMarginals μ (density (Re ∘ h) (4 · level · (v + τ))) 1 r`
--
--   hold, where `ProductBoundedMarginals μ f K r` means (OpenAI) that for every set $J$ of at most $r$ coordinates and every $x$ of positive product weight, the conditional mean of $f$ given the coordinates in $J$ is at most $K^{\lvert J\rvert}$ (here $K = 1$).
--
--   Lean: `OAI.Erdos3.stable_site_normalized_marginals_s2`, which states OpenAI's `OAI.Erdos3.stable_site_normalized_marginals` (in `lean/OAI/Combinatorics/Progressions/Probability/StableSiteDensityBounds.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B218` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Probability/StableSiteDensityBounds.lean (declaration OAI.Erdos3.stable_site_normalized_marginals)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B218

section

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem stable_site_normalized_marginals_s2 {ι σ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    {h g : (σ → ℤ) → ℂ} {lo a : σ → ℤ} {N : σ → ℕ} {M : ℕ} {q : ι → ℕ}
    [∀ i, NeZero (q i)] {r : ℕ} {level ε δ η τ : ℝ} {K : Finset ι}
    {base : ∀ i, σ → ZMod (q i)}
    (hstable : ResiduePrimeCoordinateStable g lo N M a q r δ K base)
    (hupper : PrimeRefinementUpperBound h g lo N M a q r level ε δ K base)
    (hM : 0 < M) (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
    (hcop : ∀ i ∉ K, M.Coprime (q i)) (u : ResiduePrimeCoordinateCell lo N M a q K base)
    (hg : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (g z).re ∧ (g z).re ≤ 1)
    (hh : ∀ z ∈ translatedIntegerBox lo N, |(h z).re| ≤ 1)
    (hlevel : 0 < level) (hτ : 0 < τ) (hδ : δ ≤ τ) (hε : ε ≤ level * τ)
    (hη : η < 1) (hητ : η ≤ τ) (hηlevel : η ≤ level * τ)
    (herror : ∀ S : Finset {i // i ∉ K}, S.card ≤ r →
      2 * (∑ j, ((∏ i ∈ S, q i.val : ℕ) : ℝ) /
        residueIndexLength (lo j) (lo j + N j) (M.lcm (∏ i ∈ K, q i)) ((u.val j).val)) ≤ η) :
    let v := (residuePrimeCoordinateMean g lo N M a q K base).re
    let density := fun f scale => normalizedResiduePrimeDensity lo N (M.lcm (∏ i ∈ K, q i))
      (fun j => (u.val j).val) (residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u)
      (fun i : {i // i ∉ K} => q i.val) f scale
    let μ := primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val)
    ProductBoundedMarginals μ (density (fun z => (g z).re) (2 * (v + τ))) 1 r ∧
    ProductBoundedMarginals μ (density (fun z => (h z).re) (4 * level * (v + τ))) 1 r := by
  sorry

end Erdos3

end

end OAI
end
