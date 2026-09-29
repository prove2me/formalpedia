-- Prove2me | Theorems.Thm_MasekPaterson_FourRussians_algZ_correct_finite_table
-- name    : MasekPaterson.FourRussians.algZ_correct_finite_table
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:06:57.530978+00:00
-- url     : https://prove2.me/theorems/c4dd9313-1027-4fa6-bd97-4f24bf877777
-- title:
--   The block algorithm (Algorithms Y and Z) computes $\delta(\gamma, A, B)$ from a string-independent finite table
-- statement:
--   Let $\Sigma$ be a finite alphabet and $\gamma$ a nonnegative, normalized cost function whose cost set $\Omega$ is discrete. Then there is a finite set $T \subset \mathbb{R}$ such that for every block size $m \ge 1$ and all strings $A, B$ with $m \mid |A|$ and $m \mid |B|$:
--
--   1. Algorithm Z, with $\mathrm{Fetch}$ given by Algorithm Y, returns
--   $$\mathrm{cost} = \delta(\gamma, A, B);$$
--   2. every entry of every step vector $P(i, j)$ ($1 \le i \le |A|/m$, $0 \le j \le |B|/m$) and $Q(i, j)$ ($0 \le i \le |A|/m$, $1 \le j \le |B|/m$) computed by Algorithm Z lies in $T$.
--
--   The set $T$ is chosen before $m$, $A$ and $B$. Consequently every call $\mathrm{Fetch}(P(i,j-1), Q(i-1,j), \dots)$ made by Algorithm Z is answered from the table of Algorithm Y over $\Sigma^m \times \Sigma^m \times T^m \times T^m$, a table whose size depends only on $m$, $\Sigma$ and $\gamma$ and not on the strings. These are the two facts on which the paper's running time $O(|A| \cdot |B| / \max(1, |B|/\log|A|))$ rests.
--
--   **Formalization Note** The paper states a running time $O(|A|\cdot|B|/\max(1, |B|/\log |A|))$ on a logarithmic-cost RAM; this statement formalizes the two facts the bound rests on, correctness and a string-independent finite table domain. The RAM cost model, the operation counts and the choice $m = \lfloor \log_k |A| \rfloor$ are not formalized, nor is the padding reduction for $m \nmid |A|$. The standing assumption $|A| \ge |B|$ is dropped. Algorithms Y and Z are transcribed from the pseudo-code and do not refer to $\delta$.
-- source:
--   Masek, Paterson, A Faster Algorithm Computing String Edit Distances, J. Comput. System Sci. 20, 1980, p. 24, Section 2.2, Algorithm Z (with Algorithm Y, p. 22, and Lemma 4, p. 23)

import Mathlib
import Definitions.Def_MasekPaterson_Shared_editDist
import Definitions.Def_MasekPaterson_Shared_steps
import Definitions.Def_MasekPaterson_FourRussians_algorithms
open MasekPaterson.Shared

namespace MasekPaterson.FourRussians

/-- Correctness of the Masek–Paterson block algorithm with a string-independent finite table
(§2.2, Algorithm Z with Fetch = Algorithm Y). Over a finite alphabet, for a nonnegative
normalized cost function whose cost set `Ω` is discrete, there is one finite set `T` of
reals such that for every block size `m ≥ 1` and all strings `A, B` with `m ∣ |A|` and
`m ∣ |B|`: Algorithm Z returns `δ(γ, A, B)`, and every entry of every step vector
`P(i, j)` (`1 ≤ i ≤ |A|/m`, `0 ≤ j ≤ |B|/m`) and `Q(i, j)` (`0 ≤ i ≤ |A|/m`,
`1 ≤ j ≤ |B|/m`) that Algorithm Z computes lies in `T`. -/
theorem algZ_correct_finite_table {α : Type*} [Fintype α] (γ : EditOp α → ℝ)
    (hγ : ∀ o, 0 ≤ γ o) (hN : IsNormalized γ) (hΩ : IsDiscrete γ) :
    ∃ T : Finset ℝ, ∀ m : ℕ, 0 < m → ∀ A B : List α, m ∣ A.length → m ∣ B.length →
      algZ γ m A B = editDist γ A B ∧
      (∀ i j : ℕ, 1 ≤ i → i ≤ A.length / m → j ≤ B.length / m →
        ∀ k : Fin m, algZ_P γ m A B i j k ∈ T) ∧
      (∀ i j : ℕ, i ≤ A.length / m → 1 ≤ j → j ≤ B.length / m →
        ∀ k : Fin m, algZ_Q γ m A B i j k ∈ T) := by sorry

end MasekPaterson.FourRussians
