-- Prove2me | Theorems.Thm_OnlineBeckFiala_lemma_2_6
-- name    : OnlineBeckFiala.lemma_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:33:00.850542+00:00
-- url     : https://prove2.me/theorems/6eaa8fbe-5b2e-4a28-ba2f-230b36bcd337
-- title:
--   Lemma 2.6 (Three-way coupling; Aden-Ali) — three $\{-1,0,1\}$ variables with given marginals summing to $\pm1$
-- statement:
--   For $j\in\{1,2,3\}$ let $a_j,b_j$ be reals with
--   $$0\le a_j\le\tfrac13,\qquad 0\le b_j\le\tfrac13,\qquad a_j+b_j\ge\tfrac13 .$$
--   Then there is a coupling $(\delta_1,\delta_2,\delta_3)$ of random variables with values in $\{-1,0,1\}$ such that for every $j$
--   $$P\{\delta_j=1\}=a_j,\qquad P\{\delta_j=-1\}=b_j,$$
--   and $\delta_1+\delta_2+\delta_3\in\{-1,1\}$ almost surely.
--
--   This is the finite lemma that turns three balanced walk steps into one genuine sign $\varepsilon_t=\delta_1+\delta_2+\delta_3$. The paper cites it from Aden-Ali without proof.
--
--   **Formalization Note** The coupling is given by its joint law, a probability mass function on $\{-1,0,1\}^3$ (`Fin 3 → SignType`); "almost surely" means on its support.
--
--   Differences from the source:
--   - encoding: a coupling (δ1, δ2, δ3) of random variables → a PMF on Fin 3 → SignType; a.s. = on its support; reason: a coupling of finitely-valued variables is its joint law
-- source:
--   Altschuler, Tikhomirov, Online Beck–Fiala Down to Logarithmic Sparsity, arXiv:2607.14238 (held version, sha256 5a1529d2…), p.5, Lemma 2.6

import Mathlib

namespace OnlineBeckFiala

/-- **Lemma 2.6 (Three-way coupling; [1]), p.5.** Altschuler, Tikhomirov, *Online Beck–Fiala Down to
Logarithmic Sparsity*, arXiv:2607.14238 (held version, sha256 5a1529d2…): for `j ∈ {1, 2, 3}` let
`0 ≤ a_j, b_j ≤ 1/3` with `a_j + b_j ≥ 1/3`. There is a coupling `(δ₁, δ₂, δ₃)` of `{−1, 0, 1}`-valued
random variables with `P{δ_j = 1} = a_j`, `P{δ_j = −1} = b_j` for every `j`, and
`δ₁ + δ₂ + δ₃ ∈ {−1, 1}` almost surely.

**Formalization Note.** The coupling is its joint law, a probability mass function `p` on
`Fin 3 → SignType` (indices `0, 1, 2` for `j = 1, 2, 3`); "almost surely" means on the support of `p`. -/
theorem lemma_2_6 (a b : Fin 3 → ℝ)
    (ha0 : ∀ j, 0 ≤ a j) (ha1 : ∀ j, a j ≤ 1 / 3) (hb0 : ∀ j, 0 ≤ b j) (hb1 : ∀ j, b j ≤ 1 / 3)
    (hab : ∀ j, 1 / 3 ≤ a j + b j) :
    ∃ p : PMF (Fin 3 → SignType),
      (∀ j, p.toOuterMeasure {δ | δ j = 1} = ENNReal.ofReal (a j) ∧
        p.toOuterMeasure {δ | δ j = -1} = ENNReal.ofReal (b j)) ∧
      ∀ δ ∈ p.support, (∑ j, (δ j : ℤ)) = 1 ∨ (∑ j, (δ j : ℤ)) = -1 := by sorry

end OnlineBeckFiala
