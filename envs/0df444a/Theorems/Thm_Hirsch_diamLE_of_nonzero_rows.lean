-- Prove2me | Theorems.Thm_Hirsch_diamLE_of_nonzero_rows
-- name    : Hirsch.diamLE_of_nonzero_rows
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-06T05:48:31.010354+00:00
-- url     : https://prove2.me/theorems/76e9ae85-6e0e-402e-9879-253045bac7e0
-- title:
--   A diameter bound for descriptions with nonzero normals extends to all descriptions
-- statement:
--   Fix an ambient dimension $d$ and a monotone function $\beta:\mathbb{N}\to\mathbb{N}$. Suppose that every bounded H-polytope in $\mathbb{R}^d$ described by $m$ inequalities **all of whose normals are nonzero** has combinatorial diameter at most $\beta(m)$, for every $m$. Then every bounded H-polytope in $\mathbb{R}^d$ described by $n$ inequalities, with no restriction on the normals, satisfies
--
--   $$\operatorname{DiamLE}\bigl(P,\ \beta(n)\bigr).$$
--
--   An inequality with zero normal, $\langle 0,x\rangle\le b_j$, is either vacuous (if $b_j\ge0$) and can be deleted, or unsatisfiable (if $b_j<0$), in which case $P$ is empty and the bound holds vacuously. Deleting the vacuous rows leaves a description with $m\le n$ nonzero rows and the same polytope, and monotonicity of $\beta$ together with stationary padding of walks gives the bound $\beta(n)$. This lemma lets the geometric inductions (Larman, Kalai--Kleitman) assume that every normal is nonzero, so that every row defines a genuine supporting hyperplane.
--
--   **Formalization Note** `DiamLE` allows stationary steps, hence is monotone in the bound; the hypothesis is quantified over all row counts $m$ because deletion changes the index type from `Fin n` to `Fin m`.
-- source:
--   Formalization bookkeeping for the Prove2Me Hirsch model (definition Hirsch_model, 5d9574b6-1600-4e27-9161-d12946cc4a96); the same reduction appears inside the accepted proof of Hirsch.kalai_kleitman_bound (11039061-21d8-4b92-9b38-635043c24e0d, lemmas hpoly_drop / hpoly_eq_empty).

import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace

namespace Hirsch

theorem diamLE_of_nonzero_rows (d : ℕ) (β : ℕ → ℕ) (hβ : Monotone β)
    (h : ∀ (m : ℕ) (a : Fin m → EuclideanSpace ℝ (Fin d)) (b : Fin m → ℝ), (∀ j, a j ≠ 0) →
      Bornology.IsBounded (Hpoly a b) → DiamLE (Hpoly a b) (β m))
    (n : ℕ) (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b)) :
    DiamLE (Hpoly a b) (β n) := by sorry

end Hirsch
