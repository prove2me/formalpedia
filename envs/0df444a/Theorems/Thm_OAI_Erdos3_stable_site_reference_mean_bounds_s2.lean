-- Prove2me | Theorems.Thm_OAI_Erdos3_stable_site_reference_mean_bounds_s2
-- name    : OAI.Erdos3.stable_site_reference_mean_bounds_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:36:59.119837+00:00
-- url     : https://prove2.me/theorems/f30c9935-e709-441b-b342-72fd9ae149ec
-- title:
--   On a stable residue atom, outside-coordinate conditional means of the residue densities satisfy the upper comparison and stay near the atom mean
-- statement:
--   All named objects below are defined by OpenAI.
--
--   Let $\iota, \sigma$ be finite types with decidable equality, $h, g : \mathbb{Z}^\sigma \to \mathbb{C}$, $\mathrm{lo}, a : \sigma \to \mathbb{Z}$, $N : \sigma \to \mathbb{N}$, $M \in \mathbb{N}$, $q : \iota \to \mathbb{N}$ with all $q_i \ge 1$, $r \in \mathbb{N}$, reals $\mathrm{level}, \varepsilon, \delta, \eta, \tau$, a finite set $K \subseteq \iota$ and base residues `base i : σ → ZMod (q i)`. For $I \subseteq \iota$ and residues $x$, write $\mathrm{cell}(I, x)$ for the set of integer arrays $z$ with $z_j \in [\mathrm{lo}_j, \mathrm{lo}_j + N_j)$, $z_j \equiv a_j \pmod M$, and $z \bmod q_i = x_i$ for $i \in I$, and $\mu_f(I, x)$ = `residuePrimeCoordinateMean f lo N M a q I x` for the average of $f$ over $\mathrm{cell}(I, x)$.
--
--   **Hypotheses.**
--   - `ResiduePrimeCoordinateStable g lo N M a q r δ K base`: for every finite $J$ disjoint from $K$ with $|J| \le r$ and every $y$ agreeing with `base` on $K$ with $\mathrm{cell}(K \cup J, y)$ nonempty, $\|\mu_g(K, \mathrm{base}) - \mu_g(K \cup J, y)\| \le \delta$.
--   - `PrimeRefinementUpperBound h g lo N M a q r level ε δ K base`: for the same $J, y$, $\operatorname{Re}\mu_h(K\cup J, y) \le \mathrm{level}\cdot\operatorname{Re}\mu_g(K, \mathrm{base}) + \varepsilon + \mathrm{level}\cdot\delta$.
--   - $M > 0$; the $q_i$ are pairwise coprime; $M$ is coprime to $q_i$ for every $i \notin K$; $u$ is a point of $\mathrm{cell}(K, \mathrm{base})$ (`ResiduePrimeCoordinateCell lo N M a q K base`).
--   - $|\operatorname{Re} g(z)| \le 1$ and $|\operatorname{Re} h(z)| \le 1$ for every $z$ with $z_j \in [\mathrm{lo}_j, \mathrm{lo}_j + N_j)$ for all $j$.
--   - $\mathrm{level} \ge 0$, $\tau \ge 0$, $\delta \le \tau/8$, $\varepsilon \le \mathrm{level}\cdot\tau/8$, $\eta < 1$, $\eta \le \tau/8$, $\eta \le \mathrm{level}\cdot\tau/8$.
--   - For every finite set $S$ of indices outside $K$ with $|S| \le r$,
--   $$2\sum_{j \in \sigma} \frac{\prod_{i \in S} q_i}{\texttt{residueIndexLength}\bigl(\mathrm{lo}_j,\ \mathrm{lo}_j + N_j,\ \operatorname{lcm}(M, \prod_{i \in K} q_i),\ u_j\bigr)} \le \eta,$$
--   where `residueIndexLength A B R V` is the number of integers in $[A, B)$ congruent to $V$ modulo $R$.
--
--   **Statement.** Let $v = \operatorname{Re}\mu_g(K, \mathrm{base})$. For a function $f : \mathbb{Z}^\sigma \to \mathbb{R}$ let $\mathrm{density}(f)$ = `residuePrimeCoordinateDensity lo N (lcm(M, ∏_{i∈K} q i)) u … (fun i : {i // i ∉ K} => q i) f`: the density, with respect to the product $\mu$ of uniform laws on $(\mathbb{Z}/q_i)^\sigma$ over $i \notin K$ (`primeCoordinateReference`), of the residues $(z \bmod q_i)_{i \notin K}$ of a uniform integer array $z$ with $z_j \in [\mathrm{lo}_j, \mathrm{lo}_j + N_j)$ and $z_j \equiv u_j \pmod{\operatorname{lcm}(M, \prod_{i \in K} q_i)}$, weighted by $f(z)$. Then for every finite set $S$ of indices outside $K$ with $|S| \le r$ and every point $x$,
--   $$\mathbb{E}_S[\mathrm{density}(\operatorname{Re} h)](x) \le \mathrm{level}\cdot \mathbb{E}_S[\mathrm{density}(\operatorname{Re} g)](x) + \mathrm{level}\cdot\tau \quad\text{and}\quad v - \tau \le \mathbb{E}_S[\mathrm{density}(\operatorname{Re} g)](x),$$
--   where $\mathbb{E}_S[\rho](x)$ = `productConditionalMean μ S ρ x` is the mean of $\rho$ under $\mu$ with the coordinates in $S$ fixed to those of $x$.
--
--   Lean: `OAI.Erdos3.stable_site_reference_mean_bounds_s2`, which states OpenAI's `OAI.Erdos3.stable_site_reference_mean_bounds` (in `lean/OAI/Combinatorics/Progressions/Estimates/StableRetainedAtom.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B193` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/StableRetainedAtom.lean (declaration OAI.Erdos3.stable_site_reference_mean_bounds)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B193

section

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem stable_site_reference_mean_bounds_s2 {ι σ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    {h g : (σ → ℤ) → ℂ} {lo a : σ → ℤ} {N : σ → ℕ} {M : ℕ} {q : ι → ℕ}
    [∀ i, NeZero (q i)] {r : ℕ} {level ε δ η τ : ℝ} {K : Finset ι}
    {base : ∀ i, σ → ZMod (q i)}
    (hstable : ResiduePrimeCoordinateStable g lo N M a q r δ K base)
    (hupper : PrimeRefinementUpperBound h g lo N M a q r level ε δ K base)
    (hM : 0 < M) (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
    (hcop : ∀ i ∉ K, M.Coprime (q i)) (u : ResiduePrimeCoordinateCell lo N M a q K base)
    (hg : ∀ z ∈ translatedIntegerBox lo N, |(g z).re| ≤ 1)
    (hh : ∀ z ∈ translatedIntegerBox lo N, |(h z).re| ≤ 1)
    (hlevel : 0 ≤ level) (hτ : 0 ≤ τ) (hδ : δ ≤ τ / 8) (hε : ε ≤ level * τ / 8)
    (hη : η < 1) (hητ : η ≤ τ / 8) (hηlevel : η ≤ level * τ / 8)
    (herror : ∀ S : Finset {i // i ∉ K}, S.card ≤ r →
      2 * (∑ j, ((∏ i ∈ S, q i.val : ℕ) : ℝ) /
        residueIndexLength (lo j) (lo j + N j) (M.lcm (∏ i ∈ K, q i)) ((u.val j).val)) ≤ η) :
    let v := (residuePrimeCoordinateMean g lo N M a q K base).re
    let density := fun f => residuePrimeCoordinateDensity lo N (M.lcm (∏ i ∈ K, q i))
      (fun j => (u.val j).val) (residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u)
      (fun i : {i // i ∉ K} => q i.val) f
    let μ := primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val)
    ∀ (S : Finset {i // i ∉ K}), S.card ≤ r → ∀ x,
      productConditionalMean μ S (density (fun z => (h z).re)) x ≤
        level * productConditionalMean μ S (density (fun z => (g z).re)) x + level * τ ∧
      v - τ ≤ productConditionalMean μ S (density (fun z => (g z).re)) x := by
  sorry

end Erdos3

end

end OAI
end
