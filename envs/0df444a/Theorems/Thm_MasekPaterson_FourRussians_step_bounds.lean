-- Prove2me | Theorems.Thm_MasekPaterson_FourRussians_step_bounds
-- name    : MasekPaterson.FourRussians.step_bounds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:05:34.757985+00:00
-- url     : https://prove2.me/theorems/adfe07aa-47bb-4dec-9d3c-51531f6b2648
-- title:
--   Lemma 3 — steps of an edit matrix lie in $[-I, D]$ and $[-D, I]$
-- statement:
--   Let $\gamma$ be a nonnegative cost function, and let $I, D$ be real numbers with $I_a \le I$ and $D_a \le D$ for every character $a$ (for a finite alphabet, the paper's $I = \max\{I_a \mid a \in \Sigma\}$ and $D = \max\{D_a \mid a \in \Sigma\}$). Then for all strings $A, B$ and all $i, j$ with $1 \le i \le |A|$, $1 \le j \le |B|$,
--
--   1. $-I \le \delta_{i,j} - \delta_{i-1,j} \le D$, and
--   2. $-D \le \delta_{i,j} - \delta_{i,j-1} \le I$.
--
--   The size of a step is therefore bounded independently of the strings involved, which is the first half of the finiteness of the set of steps (Lemma 4).
--
--   **Formalization Note** The paper's $I$ and $D$ are maxima over a finite alphabet; the statement is given for arbitrary upper bounds $I, D$, which implies the paper's version (take the maxima) and needs neither finiteness nor nonemptiness of the alphabet. Normalization of $\gamma$ is not assumed: the lemma holds for every nonnegative cost function.
-- source:
--   Masek, Paterson, A Faster Algorithm Computing String Edit Distances, J. Comput. System Sci. 20, 1980, p. 23, Lemma 3

import Mathlib
import Definitions.Def_MasekPaterson_Shared_editDist
open MasekPaterson.Shared

namespace MasekPaterson.FourRussians

/-- Lemma 3: if every insertion cost is at most `I` and every deletion cost at most `D`
(in particular for `I = max_a I_a`, `D = max_a D_a` over a finite alphabet), then for all
strings `A, B` and `1 ≤ i ≤ |A|`, `1 ≤ j ≤ |B|`:
(i) `−I ≤ δ_{i,j} − δ_{i−1,j} ≤ D`, and (ii) `−D ≤ δ_{i,j} − δ_{i,j−1} ≤ I`. -/
theorem step_bounds {α : Type*} (γ : EditOp α → ℝ) (hγ : ∀ o, 0 ≤ γ o)
    (I D : ℝ) (hI : ∀ a : α, insCost γ a ≤ I) (hD : ∀ a : α, delCost γ a ≤ D)
    (A B : List α) (i j : ℕ)
    (hi : 1 ≤ i) (hiA : i ≤ A.length) (hj : 1 ≤ j) (hjB : j ≤ B.length) :
    (-I ≤ dmat γ A B i j - dmat γ A B (i - 1) j ∧ dmat γ A B i j - dmat γ A B (i - 1) j ≤ D) ∧
    (-D ≤ dmat γ A B i j - dmat γ A B i (j - 1) ∧ dmat γ A B i j - dmat γ A B i (j - 1) ≤ I) := by sorry

end MasekPaterson.FourRussians
