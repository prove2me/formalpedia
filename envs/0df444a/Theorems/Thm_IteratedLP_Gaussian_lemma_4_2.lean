-- Prove2me | Theorems.Thm_IteratedLP_Gaussian_lemma_4_2
-- name    : IteratedLP.Gaussian.lemma_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:22:06.284591+00:00
-- url     : https://prove2.me/theorems/44eb384e-d7a0-4cb6-ad18-5c2151866afd
-- title:
--   Lemma 4.2 — Gaussian general position: almost surely every round has a regular KKT pair
-- statement:
--   Let $A\in\mathbb R^{M\times N}$ have i.i.d. $N(0,1/N)$ entries, let $v_1,\dots,v_K$ be i.i.d. $N(0,I_N)$ independent of $A$, and let $\kappa_1>\dots>\kappa_K$. Outside a null set of $(A,v_1,\dots,v_K)$:
--   1. every first-round KKT pair $(x,\lambda)$ is regular (Definition 4.1) whenever the optimal value $\Phi_{N,1}=v_1^\top x^{(1)}$ is positive, and then the first-round optimizer and its row multipliers are unique;
--   2. on the event $B_1\ne\emptyset$, every later round $t\le K$ of ITERATED-LP has a regular KKT pair at its iterate $x^{(t)}$, and the round-$t$ optimizer and its row multipliers are unique.
--
--   In particular $|I_t|=|F_t|$ and $A_{I_t,F_t}$ is invertible in every such round. The lemma makes each round's optimizer a nondegenerate vertex, which is what the selection density of Section 5 needs.
--
--   Differences from the source:
--
--   - generalization: M = ⌊αN⌋ rows → any numbers of rows M and columns N; reason: the null-set statement is about one fixed size; M = ⌊αN⌋ is a special case
--   - reading: on the event B_1 ≠ ∅, every later round t ≤ K has a regular KKT pair; the optimizer of every round is unique → for every run of ITERATED-LP (every choice of optimizers) with B_1 ≠ ∅ and every round t ≥ 2: a regular KKT pair at the run's iterate x^(t), every round-t optimizer equals x^(t), and the row multipliers of x^(t) are unique; reason: the rounds are those of the iterated LP; quantifying over all runs is the stronger reading and is what 'unique' asserts
--   - reading: every first-round KKT pair is regular whenever Φ_{N,1} > 0 → for every KKT pair (x, λ) of round 1 with v_1⊤x > 0: regular, the round-1 optimizer is unique and equals x, and λ is the only multiplier of x; reason: a KKT point is optimal, so v_1⊤x = Φ_{N,1}; the uniqueness clause is the lemma's 'in particular' for round 1
--   - encoding: outside a null set of the Gaussian matrix and objective vectors; A_{I_t,F_t} invertible → ∀ᵐ (A, v) under modelLaw M N K; bijectivity of the restricted linear map (Definition 4.1 item); reason: same meaning; ordering-free form of invertibility
--   - encoding: rounds t = 1, …, K → 0-based t : Fin K; round 1 is index 0 with entering iterate 0; reason: relabelling
-- source:
--   Zhang, Li, State Evolution and Universality of Iterated Linear Programs for the Binary Perceptron, arXiv:2611.04294v1, p. 17, Lemma 4.2

import Mathlib
import Definitions.Def_IteratedLP_Gaussian_Model
import Definitions.Def_IteratedLP_Gaussian_RegularKKT

open MeasureTheory ProbabilityTheory

namespace IteratedLP.Gaussian

/-- Lemma 4.2 (Gaussian general position, p. 17). For `A_ij` i.i.d. `N(0, 1/N)` and
`v_1, …, v_K` i.i.d. `N(0, I_N)` independent of `A`, and margins `κ_1 > ⋯ > κ_K`, outside a null
set of `(A, v)`:
1. every first-round KKT pair `(x, λ)` is regular whenever the optimal value
   `Φ_{N,1} = v_1⊤x` is positive; then the first-round optimizer and its row multipliers are
   unique;
2. for every run of ITERATED-LP with `B_1 ≠ ∅`, every later round `t ≤ K` has a regular KKT
   pair at its iterate `x^{(t)}`; the round-`t` optimizer and its row multipliers are unique.
(Regularity includes `|I_t| = |F_t|` and invertibility of `A_{I_t,F_t}`.) -/
theorem lemma_4_2 (M N K : ℕ) (hK : 0 < K) (κ : Fin K → ℝ) (hκ : StrictAnti κ) :
    ∀ᵐ ω ∂(modelLaw M N K),
      (∀ (x : Fin N → ℝ) (lam : Fin M → ℝ),
        IsKKTPair ω.1 (ω.2 ⟨0, hK⟩) (κ ⟨0, hK⟩) 0 x lam →
        0 < ∑ j, ω.2 ⟨0, hK⟩ j * x j →
          IsRegularKKT ω.1 (ω.2 ⟨0, hK⟩) (κ ⟨0, hK⟩) 0 x lam ∧
          (∀ x' ∈ optSet ω.1 (ω.2 ⟨0, hK⟩) (κ ⟨0, hK⟩) 0, x' = x) ∧
          (∀ lam', IsKKTPair ω.1 (ω.2 ⟨0, hK⟩) (κ ⟨0, hK⟩) 0 x lam' → lam' = lam)) ∧
      (∀ x : Fin K → Fin N → ℝ, IsRun ω.1 ω.2 κ x → (frozen (x ⟨0, hK⟩)).Nonempty →
        ∀ t : Fin K, 0 < (t : ℕ) →
          ∃ lam : Fin M → ℝ, IsRegularKKT ω.1 (ω.2 t) (κ t) (prevIter x t) (x t) lam ∧
            (∀ x' ∈ optSet ω.1 (ω.2 t) (κ t) (prevIter x t), x' = x t) ∧
            (∀ lam', IsKKTPair ω.1 (ω.2 t) (κ t) (prevIter x t) (x t) lam' → lam' = lam)) := by sorry

end IteratedLP.Gaussian
