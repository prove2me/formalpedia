-- Prove2me | Theorems.Thm_LindbladShallow_lemma_A_1
-- name    : LindbladShallow.lemma_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:17:58.833964+00:00
-- url     : https://prove2.me/theorems/59c2d29f-74e8-4e60-b36a-31595bf3b0dd
-- title:
--   Lemma A.1 — ordered jump-channel identity
-- statement:
--   For a stacked jump map $J=\sum_\mu|\mu\rangle\otimes L_\mu$ put $A_J=J^\dagger J$, $R_h=(I+hA_J/4)^{-1}$, $S_{R_h}(Z)=R_hZR_h$ and $a_J=\|A_J\|$. For every $h\ge0$ the reduced Cayley channel $\Phi_{J,h}$ (the jump Cayley gate on one fresh vacuum bath, bath traced out) satisfies
--   $$\Phi_{J,h}=\mathrm{id}+h\,\mathcal D_JS_{R_h}$$
--   (the sandwich before the dissipator), and
--   $$\|\Phi_{J,h}-\mathrm{id}-h\mathcal D_J\|_\diamond\le h^2a_J^2,\quad \|e^{h\mathcal D_J}-\mathrm{id}-h\mathcal D_J\|_\diamond\le 2h^2a_J^2,\quad \|\Phi_{J,h}-e^{h\mathcal D_J}\|_\diamond\le3h^2a_J^2.$$
--
--   This is the per-jump step error of the collision representation, used in Lemma A.4.
--
--   Differences from the source:
--   - generalization: bath of the padded dimension d_E → a bath of any dimension d + 1 (d ≥ 0 jump components); reason: the identity and bounds do not use the padding; d = d_E − 1 is the source's case
--   - encoding: bath states |0⟩, |µ⟩ → basis Fin (d+1), vacuum 0, component µ at value µ+1; reason: Lean indexing; same operators
--   - encoding: ‖Φ‖_⋄ = sup_{r≥1} sup_{Z≠0} ‖(Φ⊗I_r)(Z)‖₁/‖Z‖₁ → dnorm: an ℝ≥0∞ supremum over every r ≥ 1 and every nonzero complex Z, reference factor first (id_r ⊗ Φ), trace norm QAlgorithms.traceNorm; reason: Lean convention; reordering tensor factors changes no value and the ℝ≥0∞ supremum has no junk value
-- source:
--   Shen, Wu, Yuan, Zhang, Shallow Quantum Circuits for Geometrically Local Lindblad Dynamics, arXiv:2610.05362 (held version, sha256 8f4637ef…), Lemma A.1, pp.58–59, Eqs. (57)–(60)

import Mathlib
import Definitions.Def_LindbladShallow_gksl

open scoped Matrix ComplexOrder ENNReal

namespace LindbladShallow

/-- **Lemma A.1** (Ordered jump-channel identity; arXiv:2610.05362, held version
sha256 8f4637ef…, pp.58–59). For a stacked jump map `J = Σ_µ |µ⟩ ⊗ L_µ` put `A_J = J†J`,
`R_h = (I + hA_J/4)^{−1}`, `S_{R_h}(Z) = R_h Z R_h`, `a_J = ‖A_J‖`. For every `h ≥ 0` the reduced
Cayley channel `Φ_{J,h}` (one fresh vacuum bath) satisfies
(57) `Φ_{J,h} = id + h 𝒟_J S_{R_h}` (sandwich before the dissipator), and
(58) `‖Φ_{J,h} − id − h𝒟_J‖_⋄ ≤ h²a_J²`, (59) `‖e^{h𝒟_J} − id − h𝒟_J‖_⋄ ≤ 2h²a_J²`,
(60) `‖Φ_{J,h} − e^{h𝒟_J}‖_⋄ ≤ 3h²a_J²`.

**Formalization Note** The bath has basis `Fin (d + 1)`, vacuum `0`; `d ≥ 0` is arbitrary (the
paper's padded `d_E − 1`, and the empty jump family `d = 0`, which the proof mentions, are cases). -/
theorem lemma_A_1 {σ : Type*} [Fintype σ] [DecidableEq σ] {d : ℕ}
    (J : Matrix (Fin d × σ) σ ℂ) (h : ℝ) (hh : 0 ≤ h) :
    let AJ : Matrix σ σ ℂ := Matrix.conjTranspose J * J
    let Rh : Matrix σ σ ℂ := (1 + ((h / 4 : ℝ) : ℂ) • AJ)⁻¹
    let aJ : ℝ := opNorm AJ
    (∀ Z : Matrix σ σ ℂ, reducedJ h J Z = Z + (h : ℂ) • dissJ J (Rh * Z * Rh)) ∧
      dnorm (fun Z => reducedJ h J Z - Z - (h : ℂ) • dissJ J Z) ≤
        ENNReal.ofReal (h ^ 2 * aJ ^ 2) ∧
      dnorm (fun Z => supExp h (dissJ J) Z - Z - (h : ℂ) • dissJ J Z) ≤
        ENNReal.ofReal (2 * h ^ 2 * aJ ^ 2) ∧
      dnorm (fun Z => reducedJ h J Z - supExp h (dissJ J) Z) ≤
        ENNReal.ofReal (3 * h ^ 2 * aJ ^ 2) := by sorry

end LindbladShallow
