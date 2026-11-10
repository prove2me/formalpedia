-- Prove2me | Theorems.Thm_HarmonicCalib_Principal_proposition_D_1
-- name    : HarmonicCalib.Principal.proposition_D_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:06:36.81117+00:00
-- url     : https://prove2.me/theorems/a92bdd35-ae6a-4531-8876-dc33da550d5e
-- title:
--   Proposition D.1 — normalization correction $|h_T\Gamma(\widehat K_T) - \Gamma(K_T)| \le r(T - h_T)$
-- statement:
--   Let $A, B \subseteq \mathbb R^d$ be nonempty compact convex sets with $B = -B$, and let $r = \max_{a \in A, b \in B} \langle a, b\rangle$. For every $T \ge 1$,
--   $$\bigl| h_T\, \Gamma^{(T)}_{A,B}(\widehat K_T) - \Gamma^{(T)}_{A,B}(K_T) \bigr| \le r\,(T - h_T),$$
--   stated as the two one-sided inequalities $h_T \Gamma(\widehat K_T) \le \Gamma(K_T) + r(T-h_T)$ and $\Gamma(K_T) \le h_T\Gamma(\widehat K_T) + r(T - h_T)$.
--
--   Differences from the source:
--   - encoding: |h_T Γ(K̂_T) − Γ(K_T)| ≤ r(T − h_T) → the two one-sided inequalities, in EReal without subtraction; reason: equivalent for the finite values Γ takes on nonempty compact sets, and avoids EReal subtraction
--   - encoding: r = max_{a∈A, b∈B} ⟨a, b⟩ → every r with IsGreatest {⟨a, b⟩ : a ∈ A, b ∈ B} r; reason: the maximum exists for nonempty compact A, B and is the unique greatest element
--   - encoding: B = −B → -B = B (pointwise negation); reason: the same condition
--   - encoding: ℝ^d with the standard inner product → EuclideanSpace ℝ (Fin d) with ⟪·,·⟫_ℝ; reason: the same space; coordinates are x i for i : Fin d
--   - encoding: Γ^{(T)} and γ as real suprema → Gamma and gammaCoef valued in EReal (iSup); reason: an EReal supremum is never a junk value; on nonempty compact sets Γ is finite and the EReal comparison is the real one
-- source:
--   Fishelson and Mohri (2026), High-Dimensional Online Calibration from Harmonic Weights, arXiv:2610.07740 (version dated October 29, 2026; PDF SHA256 62ac31a3…), Proposition D.1, p. 53 (standing assumptions of Appendix D, p. 53)

import Mathlib
import Definitions.Def_HarmonicCalib_Principal_Hilbert
import Definitions.Def_HarmonicCalib_Principal_Discrepancy

open scoped InnerProductSpace Pointwise

namespace HarmonicCalib.Principal

/-- Proposition D.1 (normalization correction, p. 53): for nonempty compact convex
`A, B ⊆ ℝ^d` with `B = -B` and `r = max_{a ∈ A, b ∈ B} ⟨a, b⟩`, every `T ≥ 1` has
`|h_T Γ^{(T)}_{A,B}(K̂_T) - Γ^{(T)}_{A,B}(K_T)| ≤ r (T - h_T)`, written as the two one-sided
inequalities. -/
theorem proposition_D_1 :
    ∀ (d : ℕ) (A B : Set (EuclideanSpace ℝ (Fin d))),
      A.Nonempty → IsCompact A → Convex ℝ A →
      B.Nonempty → IsCompact B → Convex ℝ B → -B = B →
      ∀ r : ℝ, IsGreatest {x : ℝ | ∃ a ∈ A, ∃ b ∈ B, x = ⟪a, b⟫_ℝ} r →
      ∀ T : ℕ, 1 ≤ T →
        ((harm T : ℝ) : EReal) * Gamma A B T (hilbertKhat T) ≤
            Gamma A B T (hilbertK T) + ((r * ((T : ℝ) - harm T) : ℝ) : EReal) ∧
        Gamma A B T (hilbertK T) ≤
            ((harm T : ℝ) : EReal) * Gamma A B T (hilbertKhat T) +
              ((r * ((T : ℝ) - harm T) : ℝ) : EReal) := by sorry

end HarmonicCalib.Principal
