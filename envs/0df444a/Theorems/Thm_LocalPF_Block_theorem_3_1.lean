-- Prove2me | Theorems.Thm_LocalPF_Block_theorem_3_1
-- name    : LocalPF.Block.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:22:17.669366+00:00
-- url     : https://prove2.me/theorems/3989ef22-4bcc-48d2-b4a3-b5a884622998
-- title:
--   Theorem 3.1 (Dobrushin), p. 27 — if max_i Σ_j C_ij < 1, then ‖ρ − ρ̃‖_J ≤ Σ_{i∈J} Σ_j D_ij b_j with D = Σ Cⁿ
-- statement:
--   Let $I$ be a finite set, $\mathbb S=\prod_{i\in I}\mathbb S^i$ a product of Polish spaces, and $\rho,\tilde\rho$ probability measures on $\mathbb S$. Fix versions $\rho^i_\cdot$ and $\tilde\rho^i_\cdot$ of the single-site conditional distributions $\rho(X^i\in\cdot\mid X^{I\setminus\{i\}})$ and $\tilde\rho(X^i\in\cdot\mid X^{I\setminus\{i\}})$, and define
--   $$C_{ij}=\frac12\sup_{x,z\in\mathbb S:\,x^{I\setminus\{j\}}=z^{I\setminus\{j\}}}\|\rho^i_x-\rho^i_z\|,\qquad b_j=\sup_{x\in\mathbb S}\|\rho^j_x-\tilde\rho^j_x\|.$$
--   Suppose that the **Dobrushin condition** holds:
--   $$\max_{i\in I}\sum_{j\in I}C_{ij}<1.$$
--   Then the matrix series $D=\sum_{n\ge0}C^n$ converges, and for every $J\subseteq I$
--   $$\|\rho-\tilde\rho\|_J\le\sum_{i\in J}\sum_{j\in I}D_{ij}b_j.$$
--
--   This comparison theorem is the main tool of the paper's proof: it bounds the local difference of two high-dimensional measures by local differences of their single-site conditional distributions.
--
--   **Formalization Note** The statement holds for every choice of versions (the paper "fixes a version"); the versions are probability kernels satisfying the defining property of the Dobrushin definition file. $\|\cdot\|_J$ is the local norm of the Setting file with $V=I$.
-- source:
--   Rebeschini & van Handel, Can Local Particle Filters Beat the Curse of Dimensionality?, arXiv:1301.6585v2 (reprint of Ann. Appl. Probab. 25(5), 2015), pp. 26–27, Theorem 3.1

import Mathlib
import Definitions.Def_LocalPF_Block_Setting
import Definitions.Def_LocalPF_Block_Dobrushin

open MeasureTheory
open scoped ENNReal

namespace LocalPF.Block

/-- Theorem 3.1 (Dobrushin comparison theorem), p. 27, for arbitrary versions `γ`, `γ'` of the
single-site conditional distributions of `ρ`, `ρ̃`. -/
theorem theorem_3_1 {I : Type*} [Fintype I] [DecidableEq I] {Ss : I → Type*}
    [∀ i, TopologicalSpace (Ss i)] [∀ i, PolishSpace (Ss i)]
    [∀ i, MeasurableSpace (Ss i)] [∀ i, BorelSpace (Ss i)]
    (ρ ρ' : Measure (∀ i, Ss i)) [IsProbabilityMeasure ρ] [IsProbabilityMeasure ρ']
    (γ γ' : ∀ i, ProbabilityTheory.Kernel (∀ j, Ss j) (Ss i))
    [∀ i, ProbabilityTheory.IsMarkovKernel (γ i)] [∀ i, ProbabilityTheory.IsMarkovKernel (γ' i)]
    (hγ : ∀ i, IsCondVersion ρ i (γ i)) (hγ' : ∀ i, IsCondVersion ρ' i (γ' i))
    (hDob : ∀ i, ∑ j, dobC γ i j < 1) :
    ∃ D : Matrix I I ℝ, HasSum (fun n : ℕ => (Matrix.of (dobC γ)) ^ n) D ∧
      ∀ J : Finset I, locTV (J : Set I) ρ ρ' ≤
        ENNReal.ofReal (∑ i ∈ J, ∑ j, D i j * dobB γ γ' j) := by sorry

end LocalPF.Block
