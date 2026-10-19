-- Prove2me | Theorems.Thm_OAI_Erdos3_residuePhysicalTruncation_control_s2
-- name    : OAI.Erdos3.residuePhysicalTruncation_control_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:33:49.56085+00:00
-- url     : https://prove2.me/theorems/f9a98014-e9c0-4556-87e5-b037606fe8cb
-- title:
--   Close low-order product marginals of a residue box give L2 and low-degree test control of the physical ANOVA truncation
-- statement:
--   All named objects below are defined by OpenAI.
--
--   Let $\iota$ and $\sigma$ be finite types with decidable equality. Let $\mathrm{lo} : \sigma \to \mathbb{Z}$, $N : \sigma \to \mathbb{N}$, $M \in \mathbb{N}$ and $a : \sigma \to \mathbb{Z}$, such that the residue box $\mathcal{R}$ = `IntegerResidueBox lo (lo + N) M a` (integer arrays $z$ with $z_k \in [\mathrm{lo}_k, \mathrm{lo}_k + N_k)$ and $z_k \equiv a_k \pmod M$ for all $k$) is nonempty. Let $q : \iota \to \mathbb{N}$ with all $q_i \ge 1$. Let $b$ be a natural number and $f : \mathbb{Z}^\sigma \to \mathbb{R}$ with $0 \le f(z) \le 1$ for every $z$ in the box `translatedIntegerBox lo N` ($z_k \in [\mathrm{lo}_k, \mathrm{lo}_k + N_k)$). Let $\eta \ge 0$ and assume
--   `ProductMarginalsClose (primeCoordinateReference q) (residuePrimeCoordinateDensity lo N M a hne q (fun _ => 1)) η (2b)`: writing $\rho_1$ for the density, with respect to the product $\mu$ over $i \in \iota$ of the uniform laws on $(\mathbb{Z}/q_i)^\sigma$, of the residue observation $z \mapsto (z \bmod q_i)_i$ of a uniform point of $\mathcal{R}$, for every finite $S \subseteq \iota$ with $|S| \le 2b$ and every $x$, the conditional mean of $\rho_1$ given the coordinates in $S$ equal those of $x$ is within $\eta$ of $1$.
--
--   Then `ResiduePhysicalTruncationControl lo N M a hne q b f η` holds. Explicitly, let $\mathrm{low}(u)$ = `residuePhysicalTruncation lo N M a hne q b f u`, the value at the residue observation of $u$ of the ANOVA truncation (with respect to $\mu$, to coordinate sets of size at most $b$) of the density of $f$'s residue observation, and let $\mathrm{cap} = |\{S \subseteq \iota : |S| \le b\}|\cdot 2^{b}\cdot(1 + \eta)$ (`residueTruncationCap ι b η`). Then, with $\mathbb{E}_z$ the uniform average over $z \in \mathcal{R}$:
--   1. $\mathbb{E}_z\, \mathrm{low}(z)^2 \le 2 + 3\eta\,\mathrm{cap}^2$;
--   2. $\mathbb{E}_z\, (f(z) - \mathrm{low}(z))^2 \le 1 + \eta\,\mathrm{cap}^2$;
--   3. for every finite $S \subseteq \iota$ with $|S| \le b$ and every test function $t : \prod_i (\sigma \to \mathbb{Z}/q_i) \to \mathbb{R}$ that depends only on the coordinates in $S$,
--   $$\Bigl|\mathbb{E}_z\, (f(z) - \mathrm{low}(z))\cdot t\bigl((z \bmod q_i)_i\bigr)\Bigr| \le \eta\cdot\mathrm{cap}\cdot \mathbb{E}_{x \sim \mu} |t(x)|.$$
--
--   Lean: `OAI.Erdos3.residuePhysicalTruncation_control_s2`, which states OpenAI's `OAI.Erdos3.residuePhysicalTruncation_control` (in `lean/OAI/Combinatorics/Progressions/Lattices/BoundedPrimeResidual.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B193` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/BoundedPrimeResidual.lean (declaration OAI.Erdos3.residuePhysicalTruncation_control)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B193

section

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
  (hne : Nonempty (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a))
  (q : ι → ℕ) [∀ i, NeZero (q i)]

theorem residuePhysicalTruncation_control_s2 (b : ℕ) (f : (σ → ℤ) → ℝ)
    (hf : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ f z ∧ f z ≤ 1) {eta : ℝ} (heta : 0 ≤ eta)
    (hclose : ProductMarginalsClose (primeCoordinateReference (σ := σ) q)
      (residuePrimeCoordinateDensity lo N M a hne q (fun _ => 1)) eta (2 * b)) :
    ResiduePhysicalTruncationControl lo N M a hne q b f eta := by
  sorry

end Erdos3

end

end OAI
end
