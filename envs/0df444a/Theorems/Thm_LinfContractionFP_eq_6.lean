-- Prove2me | Theorems.Thm_LinfContractionFP_eq_6
-- name    : LinfContractionFP.eq_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:14:17.411697+00:00
-- url     : https://prove2.me/theorems/8be88800-21ed-442d-a8e2-85d6e293214d
-- title:
--   Eqs. (5)–(6) — the boosting potential update
-- statement:
--   Let labels $y_i\in\{\pm1\}$, integer tallies $F$ and weak labels $\ell_i\in\{\pm1\}$ be given, with potential
--   $$\Phi(F)=\sum_{i:y_i=+1}\sqrt3^{\,-F_i}+\sum_{i:y_i=-1}\sqrt3^{\,F_i}$$
--   and misclassified weight $E=\sum_{y_i=+1,\ell_i=-1}\sqrt3^{\,-F_i}+\sum_{y_i=-1,\ell_i=+1}\sqrt3^{\,F_i}$. With $F'=F+\ell$,
--   $$\Phi(F')=\tfrac1{\sqrt3}(\Phi(F)-E)+\sqrt3E=\tfrac1{\sqrt3}\Phi(F)+\Big(\sqrt3-\tfrac1{\sqrt3}\Big)E,\tag{5}$$
--   and for every $B$, if $\Phi(F)\le B$ and $E\le B/4$ then
--   $$\Phi(F')\le\tfrac{\sqrt3}{2}B.\tag{6}$$
--   Amplify uses (6) to shrink its potential budgets by $\sqrt3/2$ per round.
--
--   Differences from the source:
--   - encoding: labels in {−1, +1} → Lbl with lo = −1, hi = +1; reason: Lean convention; same instances
-- source:
--   Soleymani–Farina, A Quasipolynomial Algorithm for ℓ∞ Contractions, arXiv:2610.30122 (held version, sha256 595b44934c28fc12e2cc9cb0fb7c0750d40a24fcd5661627726f3915a24cc0de), Section 6.1, displays (5) and (6), p.13

import Mathlib
import Definitions.Def_LinfContractionFP_Lbl

open scoped Classical

namespace LinfContractionFP

/-- Displays (5) and (6), Section 6.1 (vanilla boosting): for examples with labels `y_i ∈ {±1}`,
tallies `F`, potential `Φ(F) = Σ_{y_i=+1} √3^{−F_i} + Σ_{y_i=−1} √3^{F_i}`, weak labels `ℓ` and
misclassified weight `E = Σ_{y_i=+1, ℓ_i=−1} √3^{−F_i} + Σ_{y_i=−1, ℓ_i=+1} √3^{F_i}`, the updated
tallies `F' = F + ℓ` satisfy
`Φ(F') = (1/√3)(Φ(F) − E) + √3 E = (1/√3) Φ(F) + (√3 − 1/√3) E` (5), and
`Φ(F) ≤ B, E ≤ B/4 ⟹ Φ(F') ≤ (√3/2) B` (6).

Soleymani–Farina, *A Quasipolynomial Algorithm for ℓ∞ Contractions*, arXiv:2610.30122 (held
version, sha256 595b4493…), Section 6.1, p.13: "Hence, letting F' := F + ℓ denote the updated tallies, the potential
satisfies Φ(F') = (1/√3)(Φ(F) − E) + √3 E = (1/√3)Φ(F) + (√3 − 1/√3) E. (5) [...] provided an
upper bound B on the potential Φ(F) is known, then Φ(F) ≤ B, E ≤ B/4 ⟹
Φ(F') ≤ B/√3 + (√3 − 1/√3) B/4 = (√3/2) B. (6)"

**Formalization Note.** Labels `±1` are `Lbl` (`hi` = `+1`, `lo` = `−1`); `F + ℓ` adds
`Lbl.val`. Stated over any finite set of examples, as in Section 6.1. -/
theorem eq_6 {κ : Type} [Fintype κ] (y : κ → Lbl) (F : κ → ℤ) (ℓ : κ → Lbl) :
    let Φ : (κ → ℤ) → ℝ := fun G =>
      (∑ i with y i = Lbl.hi, Real.sqrt 3 ^ (-(G i))) +
        ∑ i with y i = Lbl.lo, Real.sqrt 3 ^ (G i)
    let E : ℝ :=
      (∑ i with y i = Lbl.hi ∧ ℓ i = Lbl.lo, Real.sqrt 3 ^ (-(F i))) +
        ∑ i with y i = Lbl.lo ∧ ℓ i = Lbl.hi, Real.sqrt 3 ^ (F i)
    let F' : κ → ℤ := fun i => F i + (ℓ i).val
    (Φ F' = 1 / Real.sqrt 3 * (Φ F - E) + Real.sqrt 3 * E ∧
      Φ F' = 1 / Real.sqrt 3 * Φ F + (Real.sqrt 3 - 1 / Real.sqrt 3) * E) ∧
      ∀ B : ℝ, Φ F ≤ B → E ≤ B / 4 → Φ F' ≤ Real.sqrt 3 / 2 * B := by sorry

end LinfContractionFP
