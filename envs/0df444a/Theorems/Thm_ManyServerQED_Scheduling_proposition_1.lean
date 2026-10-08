-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_proposition_1
-- name    : ManyServerQED.Scheduling.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:46:57.466273+00:00
-- url     : https://prove2.me/theorems/b28e5bf8-73eb-4961-9f7c-531a7511e18d
-- title:
--   Proposition 1 — a feedback rule $\Psi^n=F(X^n)$ defines a unique admissible SCP
-- statement:
--   Fix $n\ge1$, an initial state $X^{0,n}\in\mathbb Z^k_+$ and a map $F:\mathbb Z^k_+\to\mathbb Z^k_+$ such that, for every $X\in\mathbb Z^k_+$,
--   $$
--   X-F(X)\in\mathbb Z^k_+\qquad\text{and}\qquad\mathbb 1\cdot F(X)\le n.
--   $$
--   Then the system equations (7) together with the feedback rule
--   $$
--   \Psi^n(t)=F(X^n(t)),\qquad t\ge0,\qquad(11)
--   $$
--   have a unique solution $X^n$, and $\Psi^n$ is an admissible scheduling control policy.
--
--   Proposition 1 is how the proposed policy, which is of this feedback form, becomes an admissible SCP.
--
--   **Formalization Note** Solutions are $\mathbb Z^k_+$-valued processes (so that $F(X^n(t))$ makes sense). Uniqueness is pathwise, for every $\omega$ and every $t\ge0$, under the model's convention that every sample path of the primitives is regular. The final sentence of the proposition (an admissible SCP whose $B^n$ is nondecreasing is an admissible N-SCP) holds by the definition of an N-SCP and is not formalized separately. The paper gives only a proof sketch in Appendix A.3.
-- source:
--   Atar, Mandelbaum & Reiman, Scheduling a Multi Class Queue with Many Exponential Servers: Asymptotic Optimality in Heavy Traffic, arXiv:math/0407058v1 (reprint of Ann. Appl. Probab. 14(3), 2004), p. 12, Proposition 1 (proof sketch pp. 48-50)

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_ManyServerQED_Scheduling_Diffusion
import Definitions.Def_ManyServerQED_Scheduling_Model
import Definitions.Def_ManyServerQED_Scheduling_Policy

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ManyServerQED.Scheduling

/-- Proposition 1 (p. 12): fix `n ≥ 1` and `F : ℤ^k_+ → ℤ^k_+` with `X − F(X) ∈ ℤ^k_+` and
`𝟙 · F(X) ≤ n`. Then the system (7), (11) `Ψⁿ(t) = F(Xⁿ(t))` has a unique solution (for every `ω`,
among `ℤ^k_+`-valued processes), and `Ψⁿ` is an admissible SCP. -/
theorem proposition_1 {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (M : SystemSequence Ω k) (n : ℕ)
    (hn : 1 ≤ n) (X0 : Fin k → ℕ) (F : (Fin k → ℕ) → (Fin k → ℕ))
    (hF_le : ∀ X i, F X i ≤ X i) (hF_sum : ∀ X, ∑ i, F X i ≤ n) :
    ∃ X : Ω → ℝ → Fin k → ℕ,
      M.IsControlled n X0 (fun ω t i => (X ω t i : ℝ)) (fun ω t i => (F (X ω t) i : ℝ)) ∧
      (∀ Y : Ω → ℝ → Fin k → ℕ,
        M.IsControlled n X0 (fun ω t i => (Y ω t i : ℝ)) (fun ω t i => (F (Y ω t) i : ℝ)) →
          ∀ ω t, 0 ≤ t → Y ω t = X ω t) ∧
      M.IsSCP n X0 (fun ω t i => (X ω t i : ℝ)) (fun ω t i => (F (X ω t) i : ℝ)) ∧
      M.IsAdmissible n (fun ω t i => (X ω t i : ℝ)) (fun ω t i => (F (X ω t) i : ℝ)) := by sorry

end ManyServerQED.Scheduling
