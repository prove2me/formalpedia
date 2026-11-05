-- Prove2me | Theorems.Thm_FowlerLSQC_Canonical_canonical_decomposition
-- name    : FowlerLSQC.Canonical.canonical_decomposition
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:36:46.856079+00:00
-- url     : https://prove2.me/theorems/609928eb-ebdb-4537-9955-c8fbce50cb51
-- title:
--   Every two-qubit gate has a canonical decomposition with a unique $\vec\theta$
-- statement:
--   Let $G\in U(4)$ be an arbitrary two-qubit gate. Then:
--   1. (**existence**) there are single-qubit gates $G_{1A},G_{1B},G_{2A},G_{2B}\in U(2)$ and $\vec\theta=(\theta_1,\theta_2,\theta_3)\in\mathbb R^3$ with
--   $$
--   G\cong(G_{2A}\otimes G_{2B})\,G_{\vec\theta}\,(G_{1A}\otimes G_{1B}),\qquad G_{\vec\theta}=e^{i(\theta_1X\otimes X+\theta_2Y\otimes Y+\theta_3Z\otimes Z)},
--   $$
--   ($\cong$ = equality up to global phase) such that
--   $$
--   \theta_1\ge\theta_2,\quad \tfrac\pi2-\theta_1\ge\theta_2,\quad \theta_2\ge\theta_3,\quad \theta_3\ge0,\quad\text{and }\tfrac\pi2-\theta_1\ge\theta_1\text{ if }\theta_3=0;
--   $$
--   2. (**uniqueness**) the vector $\vec\theta$ is unique: if $\vec\theta$ and $\vec\theta'$ both satisfy these conditions and both occur in such a decomposition of $G$ (with any single-qubit gates and any global phases), then $\vec\theta=\vec\theta'$.
--
--   The vector $\vec\theta$ is therefore a complete invariant of two-qubit gates up to single-qubit gates and phase, and the thesis uses it to synthesize arbitrary two-qubit gates from physical interactions.
--
--   **Formalization Note** $G$ ranges over `Matrix.unitaryGroup (Bool × Bool) ℂ`, all of $U(4)$. Uniqueness concerns $\vec\theta$ only; the single-qubit gates and the phase may differ between two decompositions.
--
--   Differences from the source:
--   - reading: "The canonical decomposition can be made unique" → existence of a decomposition with $\vec\theta$ satisfying the conditions, and uniqueness of $\vec\theta$ only; reason: the single-qubit gates are not unique (p.51: "unique up to a possible mutual sign flip"; global phases can be moved between factors), so "unique" refers to $\vec\theta$, as p.53 says ("the unique $\vec\theta$ described above").
--   - encoding: $\theta_1,\theta_2,\theta_3$ → `θ 0, θ 1, θ 2`; "equality up to global phase" → $\exists\varphi\in\mathbb R,\ G=e^{i\varphi}(\cdots)$; reason: Lean convention, same instances.
-- source:
--   Fowler, Towards Large-Scale Quantum Computation, arXiv:quant-ph/0506126v1, §4.2, (4.4), pp.48–49 (PDF pp.66–67); §4.4, p.53 (PDF p.71)

import Mathlib
import Definitions.Def_FowlerLSQC_Canonical_InChamber
import Definitions.Def_FowlerLSQC_Canonical_IsCanonicalDecomposition

namespace FowlerLSQC.Canonical

/-- Fowler, *Towards Large-Scale Quantum Computation*, arXiv:quant-ph/0506126v1, §4.2, (4.4),
pp.48–49 (PDF pp.66–67), and §4.4, p.53 (PDF p.71): every two-qubit gate `G ∈ U(4)` has a
canonical decomposition `G ≅ (G2A ⊗ G2B) G_θ (G1A ⊗ G1B)` with `G1A, G1B, G2A, G2B ∈ U(2)` and
`θ` satisfying `θ1 ≥ θ2`, `π/2 − θ1 ≥ θ2`, `θ2 ≥ θ3`, `θ3 ≥ 0`, and `π/2 − θ1 ≥ θ1` if `θ3 = 0`;
and the `θ` with these properties is unique.

**Formalization Note.** `∃!` asserts existence and uniqueness of `θ` only: the single-qubit
factors and the global phase may differ between two decompositions (the book: "unique up to a
possible mutual sign flip", p.51). `G` ranges over all of `U(4)`
(`Matrix.unitaryGroup (Bool × Bool) ℂ`), not only `SU(4)`. -/
theorem canonical_decomposition (G : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (hG : G ∈ Matrix.unitaryGroup (Bool × Bool) ℂ) :
    ∃! θ : Fin 3 → ℝ, InChamber θ ∧
      ∃ G1A G1B G2A G2B : Matrix.unitaryGroup Bool ℂ,
        IsCanonicalDecomposition G G1A G1B G2A G2B θ := by sorry

end FowlerLSQC.Canonical
