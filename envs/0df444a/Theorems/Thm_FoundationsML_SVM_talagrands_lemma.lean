-- Prove2me | Theorems.Thm_FoundationsML_SVM_talagrands_lemma
-- name    : FoundationsML.SVM.talagrands_lemma
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T21:30:44.136292+00:00
-- url     : https://prove2.me/theorems/f500f416-47b0-44e4-a823-3d23c4002f28
-- title:
--   Lemma 5.7 — Talagrand's lemma
-- statement:
--   **Statement (Lemma 5.7, p. 93, PDF p. 110).** Let $\Phi_1,\dots,\Phi_m$ be $l$-Lipschitz
--   functions from $\mathbb R$ to $\mathbb R$ and $\sigma_1,\dots,\sigma_m$ be Rademacher random
--   variables. Then, for any hypothesis set $H$ of real-valued functions,
--   $$\frac1m\,\mathbb E_\sigma\Big[\sup_{h\in H}\sum_{i=1}^m \sigma_i(\Phi_i\circ h)(x_i)\Big]
--     \le \frac lm\,\mathbb E_\sigma\Big[\sup_{h\in H}\sum_{i=1}^m \sigma_i h(x_i)\Big]
--     = l\,\hat R_S(H).$$
--
--   This is the key tool that lets the margin loss's $1/\rho$-Lipschitz surrogate $\Phi_\rho$
--   be pulled out of the Rademacher complexity in the proof of Theorem 5.8.
--
--   **Formalization Note.** The left-hand side is written with the same finite-average template
--   as `EmpiricalRademacherComplexity` (footnote 3, p. 30) applied to `Φ_i ∘ h` in place of `h`;
--   the right-hand side is `l * EmpiricalRademacherComplexity H S`. The Lipschitz hypothesis
--   `hLip` is a genuine two-sided bound `|Φ_i x - Φ_i y| ≤ l * |x - y|` applied uniformly to
--   every `i ∈ Fin m` with the same constant `l`, per `BRIEF.md`'s pitfall note (not a
--   per-index constant later maximized).
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 93, Lemma 5.7 (PDF p. 110)

import Mathlib
import Definitions.Def_FoundationsML_SVM_EmpiricalRademacherComplexity

namespace FoundationsML.SVM

/-- Lemma 5.7 (Talagrand's lemma; Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine
Learning*, 2nd ed., MIT Press 2018, p. 93, PDF p. 110). Let `Φ_1, …, Φ_m` be `l`-Lipschitz
functions from `ℝ` to `ℝ` and `σ_1, …, σ_m` be Rademacher random variables. Then, for any
hypothesis set `H` of real-valued functions,
`(1/m) E_σ[sup_{h∈H} ∑_{i=1}^m σ_i (Φ_i∘h)(x_i)] ≤ (l/m) E_σ[sup_{h∈H} ∑_{i=1}^m σ_i h(x_i)]
= l·R̂_S(H)`.

**Formalization Note.** The left-hand side is written out with the same finite-average
template as `EmpiricalRademacherComplexity` (footnote 3, p. 30), applied to `Φ_i ∘ h` in
place of `h`; the right-hand side is `l * EmpiricalRademacherComplexity H S`, matching the
book's own rewriting of the right-hand expectation as `l·R̂_S(H)`. -/
theorem talagrands_lemma {X : Type*} {m : ℕ} (H : Set (X → ℝ)) (S : Fin m → X)
    (Φ : Fin m → ℝ → ℝ) (l : ℝ) (hl : 0 ≤ l)
    (hLip : ∀ i : Fin m, ∀ x y : ℝ, |Φ i x - Φ i y| ≤ l * |x - y|) :
    (1 / (2 : ℝ) ^ m) * ∑ σ : Fin m → Bool,
      ⨆ h ∈ H, (1 / (m : ℝ)) * ∑ i : Fin m, (if σ i then (1 : ℝ) else -1) * Φ i (h (S i))
      ≤ l * EmpiricalRademacherComplexity H S := by sorry

end FoundationsML.SVM
