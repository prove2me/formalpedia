-- Prove2me | Theorems.Thm_OAI_Erdos3_unconditioned_affine_cell_bounds_s2
-- name    : OAI.Erdos3.unconditioned_affine_cell_bounds_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:35:10.312146+00:00
-- url     : https://prove2.me/theorems/3b84c62f-a7c0-42f2-ae54-ddf899671c46
-- title:
--   Long boxes give close low-order prime-coordinate marginals, nonempty residue cells, and long cell sides
-- statement:
--   Let $\iota, \sigma$ be finite types with decidable equality, $|\sigma|$ the number of elements of $\sigma$. Let $\mathrm{lo} : \sigma \to \mathbb{Z}$, $N : \sigma \to \mathbb{N}$ and $a : \sigma \to \mathbb{Z}$, and assume the box `IntegerResidueBox lo (lo + N) 1 a` (defined by OpenAI: the tuples $z \in \mathbb{Z}^{\sigma}$ with $\mathrm{lo}_k \le z_k < \mathrm{lo}_k + N_k$ for all $k$ and $z_k \equiv a_k \pmod 1$, which is no condition) is nonempty. Let $q : \iota \to \mathbb{N}$ be nonzero and pairwise coprime. Let $A \le B$ be natural numbers and $\varepsilon, L, T, C, \mathrm{modLog}, \mathrm{dimLog}$ real numbers with $L, T, C, \mathrm{modLog}, \mathrm{dimLog} \ge 0$ ($\varepsilon$ is arbitrary), $q_i \le e^{\mathrm{modLog}}$ for every $i$, $|\sigma| \le e^{\mathrm{dimLog}}$, and
--   $$\exp\bigl(\mathrm{modLog}\cdot A + \Lambda + 2\bigr) \le N_k \quad\text{for every } k \in \sigma,$$
--   where $\Lambda$ = `affineComparisonLengthLog B ε L T C modLog dimLog`, an explicit real quantity defined by OpenAI. Then the following three statements hold.
--
--   1. `ProductMarginalsClose (primeCoordinateReference q) ρ η A` holds, where $\rho$ = `residuePrimeCoordinateDensity lo N 1 a hne q (fun _ => 1)` and $\eta$ = `affineComparisonAccuracy B (affineComparisonScale ε L T C) L T` (explicit real quantities of OpenAI; $\eta = \exp(-((P+3)^3 + 2B(P+2) + L + T + 4))$ with $P$ = `affineComparisonScale ε L T C`). Here `primeCoordinateReference q i` is the uniform probability distribution on $(\mathbb{Z}/q_i\mathbb{Z})^{\sigma}$; $\rho$ is the density, with respect to the product $\pi$ of these uniform distributions, of the distribution of the residue tuple $(z \bmod q_i)_{i \in \iota}$ when $z$ is uniform on the box (that is, $\rho(y) = \Pr_z[(z \bmod q_i)_i = y]/\pi(y)$); and `ProductMarginalsClose` (defined by OpenAI) says: for every $S \subseteq \iota$ with $|S| \le A$ and every $x$ with $\pi(x) \ne 0$, $\bigl|\mathbb{E}_{y \sim \pi}\,\rho(x|_S, y|_{\iota \setminus S}) - 1\bigr| \le \eta$, where $(x|_S, y|_{\iota\setminus S})$ agrees with $x$ on $S$ and with $y$ off $S$.
--   2. For every $K \subseteq \iota$ with $|K| \le A$ and every $\mathrm{base} \in \prod_i (\mathbb{Z}/q_i\mathbb{Z})^{\sigma}$, the cell `ResiduePrimeCoordinateCell lo N 1 a q K base` is nonempty, i.e. there is a point $z$ of the box with $z \bmod q_i = \mathrm{base}_i$ for every $i \in K$.
--   3. For every such $K$ and $\mathrm{base}$, every point $u$ of that cell and every $k \in \sigma$,
--   $$e^{\Lambda} \le \texttt{residueIndexLength}\ (\mathrm{lo}_k)\ (\mathrm{lo}_k + N_k)\ \bigl(\operatorname{lcm}(1, \textstyle\prod_{i \in K} q_i)\bigr)\ (u_k),$$
--   where `residueIndexLength a b r v` $= \max\bigl(0, \lceil (b-v)/r \rceil - \lceil (a-v)/r \rceil\bigr)$ (defined by OpenAI), which for $r > 0$ is the number of integers in $[a, b)$ congruent to $v$ modulo $r$.
--
--   Lean: `OAI.Erdos3.unconditioned_affine_cell_bounds_s2`, which states OpenAI's `OAI.Erdos3.unconditioned_affine_cell_bounds` (in `lean/OAI/Combinatorics/Progressions/Lattices/InitialMaskedAffineComparison.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B193` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/InitialMaskedAffineComparison.lean (declaration OAI.Erdos3.unconditioned_affine_cell_bounds)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B193

section

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem unconditioned_affine_cell_bounds_s2 {ι σ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (1 : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
    {A B : ℕ} (hAB : A ≤ B) {ε L T C modLog dimLog : ℝ}
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hC : 0 ≤ C) (hmodLog : 0 ≤ modLog) (hdimLog : 0 ≤ dimLog)
    (hmoduli : ∀ i, (q i : ℝ) ≤ Real.exp modLog)
    (hdim : (Fintype.card σ : ℝ) ≤ Real.exp dimLog)
    (hside : ∀ k, Real.exp (modLog * A + affineComparisonLengthLog B ε L T C modLog dimLog + 2) ≤ (N k : ℝ)) :
    ProductMarginalsClose (primeCoordinateReference (σ := σ) q)
      (residuePrimeCoordinateDensity lo N 1 a hne q (fun _ => 1))
      (affineComparisonAccuracy B (affineComparisonScale ε L T C) L T) A ∧
    (∀ (K : Finset ι), K.card ≤ A → ∀ base : ∀ i, σ → ZMod (q i),
      Nonempty (ResiduePrimeCoordinateCell lo N 1 a q K base)) ∧
    (∀ (K : Finset ι), K.card ≤ A → ∀ (base : ∀ i, σ → ZMod (q i))
      (u : ResiduePrimeCoordinateCell lo N 1 a q K base) (k : σ),
      Real.exp (affineComparisonLengthLog B ε L T C modLog dimLog) ≤
        (residueIndexLength (lo k) (lo k + N k) (Nat.lcm 1 (∏ i ∈ K, q i)) ((u.val k).val) : ℝ)) := by
  sorry

end Erdos3

end

end OAI
end
