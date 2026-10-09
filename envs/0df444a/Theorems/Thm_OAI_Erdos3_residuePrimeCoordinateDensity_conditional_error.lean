-- Prove2me | Theorems.Thm_OAI_Erdos3_residuePrimeCoordinateDensity_conditional_error
-- name    : OAI.Erdos3.residuePrimeCoordinateDensity_conditional_error
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T17:31:35.845728+00:00
-- url     : https://prove2.me/theorems/9881983c-00dc-490a-bd21-00e851756898
-- title:
--   Conditional means of the prime-coordinate density are close to cell averages
-- statement:
--   Let $\iota$ and $\sigma$ be finite types with decidable equality. Let $\mathrm{lo} : \sigma \to \mathbb{Z}$, $N : \sigma \to \mathbb{N}$, $M \in \mathbb{N}$ and $a : \sigma \to \mathbb{Z}$ be such that the residue box $\mathcal{B} = $ `IntegerResidueBox lo (lo + N) M a` — the finite set of $z : \sigma \to \mathbb{Z}$ with $\mathrm{lo}_j \le z_j < \mathrm{lo}_j + N_j$ and $z_j \equiv a_j \pmod M$ for all $j$ — is nonempty (`hne`). Let $q : \iota \to \mathbb{N}$ take nonzero values, with $0 < M$, $M$ coprime to every $q_i$, and the $q_i$ pairwise coprime. On $X = \prod_{i \in \iota} (\sigma \to \mathbb{Z}/q_i)$ let $\mu$ be the product of the uniform weights `primeCoordinateReference q i`, and for $z \in \mathcal{B}$ let $\mathrm{obs}(z) = (z \bmod q_i)_i$. For $f : (\sigma \to \mathbb{Z}) \to \mathbb{R}$, `residuePrimeCoordinateDensity lo N M a hne q f` is the function $\rho_f : X \to \mathbb{R}$, $\rho_f(y) = \mathbb{E}_{z \in \mathcal{B}}\bigl[f(z)\, \mathbf{1}\{\mathrm{obs}(z) = y\}\bigr] / \mu(y)$, $z$ uniform. Let $C \ge 0$ with $|f(z)| \le C$ on the box `translatedIntegerBox lo N` $= \{\mathrm{lo} + y : 0 \le y_j < N_j\}$, let $I \subseteq \iota$ be finite and $x \in X$, and suppose
--   $$s := \sum_{j \in \sigma} \frac{\prod_{i \in I} q_i}{\texttt{residueIndexLength}(\mathrm{lo}_j,\ \mathrm{lo}_j + N_j,\ M,\ a_j)} \le \frac12,$$
--   where `residueIndexLength l h M v` $= \max\bigl(0, \lceil (h - v)/M \rceil - \lceil (l - v)/M \rceil\bigr)$ and division by $0$ gives $0$. Then
--   $$\Bigl|\,\texttt{productConditionalMean}\ \mu\ I\ \rho_f\ x - \mathbb{E}_{z \in \mathcal{C}} f(z)\Bigr| \le 2 s C,$$
--   where `productConditionalMean μ I ρ x` $= \mathbb{E}_{y \sim \mu}\, \rho(x|_I, y|_{\iota \setminus I})$ (the point equal to $x$ on the coordinates in $I$ and to $y$ elsewhere), and $\mathcal{C} = $ `ResiduePrimeCoordinateCell lo N M a q I x` is the set of $z \in \mathcal{B}$ with $z \bmod q_i = x_i$ for every $i \in I$ (an average over the empty set being $0$).
--
--   Lean: `OAI.Erdos3.residuePrimeCoordinateDensity_conditional_error` in `lean/OAI/Combinatorics/Progressions/Lattices/ResiduePrimeDensityError.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B090` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/ResiduePrimeDensityError.lean#L596

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090

namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
  (hne : Nonempty (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a))
  (q : ι → ℕ) [∀ i, NeZero (q i)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem residuePrimeCoordinateDensity_conditional_error {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (hM : 0 < M) (hcop : ∀ i, M.Coprime (q i))
    (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
    (f : (σ → ℤ) → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ z ∈ translatedIntegerBox lo N, |f z| ≤ C)
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i))
    (hsmall : (∑ j, ((∏ i ∈ I, q i : ℕ) : ℝ) /
      residueIndexLength (lo j) (lo j + N j) M (a j)) ≤ 1 / 2) :
    |productConditionalMean (primeCoordinateReference (σ := σ) q) I
      (residuePrimeCoordinateDensity lo N M a hne q f) x -
        (𝔼 z : ResiduePrimeCoordinateCell lo N M a q I x, f (fun j => (z.val j).val))| ≤
      (2 * ∑ j, ((∏ i ∈ I, q i : ℕ) : ℝ) /
        residueIndexLength (lo j) (lo j + N j) M (a j)) * C := by
  sorry

end Erdos3
end
end OAI
