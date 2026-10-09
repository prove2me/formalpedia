-- Prove2me | Theorems.Thm_OAI_Erdos3_residuePrimeCoordinateCell_nonempty_of_small
-- name    : OAI.Erdos3.residuePrimeCoordinateCell_nonempty_of_small
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T17:59:37.244867+00:00
-- url     : https://prove2.me/theorems/e624a611-8a1e-4c21-8e06-ce7e77d68a20
-- title:
--   A prime-coordinate cell of a residue box is nonempty when the moduli are small
-- statement:
--   Let $\iota$ and $\sigma$ be finite types with decidable equality. Let $\mathrm{lo} : \sigma \to \mathbb{Z}$, $N : \sigma \to \mathbb{N}$, $M \in \mathbb{N}$ and $a : \sigma \to \mathbb{Z}$ be such that the residue box `IntegerResidueBox lo (lo + N) M a` — the finite set of $z : \sigma \to \mathbb{Z}$ with $\mathrm{lo}_j \le z_j < \mathrm{lo}_j + N_j$ and $z_j \equiv a_j \pmod M$ for all $j$ — is nonempty. Let $q : \iota \to \mathbb{N}$ take nonzero values, with $0 < M$, $M$ coprime to every $q_i$, and the $q_i$ pairwise coprime. Let $I$ be a finite subset of $\iota$ and $x \in \prod_{i \in \iota} (\sigma \to \mathbb{Z}/q_i)$, and suppose
--   $$\sum_{j \in \sigma} \frac{\prod_{i \in I} q_i}{\ell_j} < \frac12, \qquad \ell_j = \texttt{residueIndexLength}(\mathrm{lo}_j,\ \mathrm{lo}_j + N_j,\ M,\ a_j),$$
--   where `residueIndexLength l h M v` $= \max\bigl(0, \lceil (h - v)/M \rceil - \lceil (l - v)/M \rceil\bigr)$ (a natural number, the number of integers in $[l, h)$ congruent to $v$ mod $M$ when $M > 0$), and division by $0$ gives $0$. Then the cell `ResiduePrimeCoordinateCell lo N M a q I x` — the set of $z$ in the residue box with $z \bmod q_i = x_i$ coordinatewise for every $i \in I$ — is nonempty.
--
--   Lean: `OAI.Erdos3.residuePrimeCoordinateCell_nonempty_of_small` in `lean/OAI/Combinatorics/Progressions/Lattices/ResiduePrimeDensityError.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B090` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/ResiduePrimeDensityError.lean#L506

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

theorem residuePrimeCoordinateCell_nonempty_of_small {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (hM : 0 < M) (hcop : ∀ i, M.Coprime (q i))
    (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i))
    (hsmall : (∑ j, ((∏ i ∈ I, q i : ℕ) : ℝ) /
      residueIndexLength (lo j) (lo j + N j) M (a j)) < 1 / 2) :
    Nonempty (ResiduePrimeCoordinateCell lo N M a q I x) := by
  sorry

end Erdos3
end
end OAI
