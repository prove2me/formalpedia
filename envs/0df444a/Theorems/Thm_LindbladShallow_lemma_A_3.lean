-- Prove2me | Theorems.Thm_LindbladShallow_lemma_A_3
-- name    : LindbladShallow.lemma_A_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:17:45.046869+00:00
-- url     : https://prove2.me/theorems/8e69875a-2ab5-4d9e-b40b-e5f1bbb5b3e7
-- title:
--   Lemma A.3 — positive-time product formula
-- statement:
--   For finite-dimensional GKSL generators $\mathcal L_1,\dots,\mathcal L_m$ on a common space and $h\ge0$,
--   $$\Big\|e^{h\mathcal L_m}\cdots e^{h\mathcal L_1}-e^{h\sum_e\mathcal L_e}\Big\|_\diamond\le\frac{h^2}{2}\sum_{e<f}\|[\mathcal L_e,\mathcal L_f]\|_\diamond.$$
--
--   This first-order Trotter bound compares one ordered collision period with the semigroup $e^{h\mathcal L}$ in Lemma A.4.
--
--   Differences from the source:
--   - encoding: e^{hℒ_m} ⋯ e^{hℒ_1} → the composition with ℒ_1 applied first, as a product in the algebra of linear maps; reason: Lean convention; same map
--   - encoding: ‖Φ‖_⋄ = sup_{r≥1} sup_{Z≠0} ‖(Φ⊗I_r)(Z)‖₁/‖Z‖₁ → dnorm: an ℝ≥0∞ supremum over every r ≥ 1 and every nonzero complex Z, reference factor first (id_r ⊗ Φ), trace norm QAlgorithms.traceNorm; reason: Lean convention; reordering tensor factors changes no value and the ℝ≥0∞ supremum has no junk value
-- source:
--   Shen, Wu, Yuan, Zhang, Shallow Quantum Circuits for Geometrically Local Lindblad Dynamics, arXiv:2610.05362 (held version, sha256 8f4637ef…), Lemma A.3, p.60, Eq. (62)

import Mathlib
import Definitions.Def_LindbladShallow_gksl

open scoped Matrix ComplexOrder ENNReal

namespace LindbladShallow

/-- **Lemma A.3** (Positive-time product formula; arXiv:2610.05362, held version
sha256 8f4637ef…, p.60). For finite-dimensional GKSL generators `ℒ_1, …, ℒ_m` and `h ≥ 0`,
`‖e^{hℒ_m} ⋯ e^{hℒ_1} − e^{h Σ_e ℒ_e}‖_⋄ ≤ (h²/2) Σ_{e<f} ‖[ℒ_e, ℒ_f]‖_⋄` (62).

**Formalization Note** The product is the composition `e^{hℒ_m} ∘ ⋯ ∘ e^{hℒ_1}` (`ℒ_1` first);
`[ℒ_e, ℒ_f] = ℒ_e ∘ ℒ_f − ℒ_f ∘ ℒ_e`. -/
theorem lemma_A_3 {n : Type*} [Fintype n] [DecidableEq n] {m : ℕ}
    (L : Fin m → (Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)) (hL : ∀ e, IsGKSL (L e))
    (h : ℝ) (hh : 0 ≤ h) :
    dnorm (⇑((List.ofFn fun e => supExp h (L e)).reverse.prod) - ⇑(supExp h (∑ e, L e))) ≤
      ENNReal.ofReal (h ^ 2 / 2) *
        ∑ e : Fin m, ∑ f : Fin m, if e < f then dnorm ⇑(L e * L f - L f * L e) else 0 := by sorry

end LindbladShallow
