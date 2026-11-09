-- Prove2me | Theorems.Thm_LeeYangGap_SpectralGap_partition_size_bounds
-- name    : LeeYangGap.SpectralGap.partition_size_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:12:40.622261+00:00
-- url     : https://prove2.me/theorems/78338972-c561-4be2-8294-6d8a61ed8f57
-- title:
--   Lemma 3 — Size bounds of the Trotterized partition function
-- statement:
--   Let $H$ be a Lee–Yang Hamiltonian on $n\ge1$ qubits, $\beta>0$, $M\ge1$, $\epsilon=\beta/M$, $W=\sum_{ij}w^z_{ij}$ and $L=\prod_{ij}e^{-\epsilon H_{ij}/2}$. For the all-zero basis vector $|0\rangle$, the actual Trotter trace polynomial obeys all three assertions
--   $$\mathcal Z_\epsilon(0)=\|L|0\rangle\|^{2M},\qquad |\log\mathcal Z_\epsilon(0)|\le3\beta W,\qquad |\mathcal Z_\epsilon(y)|\le2^ne^{3\beta W}\quad(\forall l,\ |y_l|\le1).$$
--   The vector norm is Euclidean and the center logarithm is real since $\mathcal Z_\epsilon(0)>0$. The last clause is the pointwise form of the closed-unit-polydisc supremum bound. These are the source's center normalization and global size controls.
--
--   Differences from the source:
--   - encoding: finite qubit Hilbert space and site indices → complex matrices indexed by Fin n → Fin 2, with finite ordered bond lists; reason: the computational basis and bond order are explicit; arbitrary finite graphs are represented, with no coefficient restriction added
--   - encoding: supremum bound over a closed polydisc → the same bound at every point of the closed polydisc; reason: equivalent bound without default values of real suprema
-- source:
--   Chaithanya Rayudu, Jun Takahashi, Spectral gap of Lee-Yang Hamiltonians, STOC 2027 submission #575 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/575.pdf, Lemma 3, printed/PDF p. 5

import Mathlib
import Definitions.Def_LeeYangGap_SpectralGap_Analytic
open scoped BigOperators Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false
noncomputable section

namespace LeeYangGap.SpectralGap

/-- Rayudu–Takahashi, STOC 2027 submission #575; source index in items.yaml. -/
theorem partition_size_bounds {n : ℕ} (hn : 0 < n) (B : System n) (hLY : IsLeeYang B)
    (β : ℝ) (hβ : 0 < β) (M : ℕ) (hM : 1 ≤ M) :
    trotterPartition B β M 0 =
      ((‖(WithLp.toLp 2 ((layerL B (stepSize β M)) *ᵥ
        (fun x : Config n => if x = (fun _ => 0) then 1 else 0)) :
          EuclideanSpace ℂ (Config n))‖ : ℝ) : ℂ)^(2*M) ∧
    |Real.log (trotterPartition B β M 0).re| ≤ 3 * β * weight B ∧
    ∀ y : LayerVariables n M, (∀ l, ‖y l‖ ≤ 1) →
      ‖trotterPartition B β M y‖ ≤ 2^n * Real.exp (3 * β * weight B) := by sorry
end LeeYangGap.SpectralGap
