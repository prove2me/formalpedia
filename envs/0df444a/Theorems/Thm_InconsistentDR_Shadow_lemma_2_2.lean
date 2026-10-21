-- Prove2me | Theorems.Thm_InconsistentDR_Shadow_lemma_2_2
-- name    : InconsistentDR.Shadow.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:59:27.931917+00:00
-- url     : https://prove2.me/theorems/b3bac1fc-a405-449f-ae09-5909cc3d6d58
-- title:
--   Lemma 2.2, p. 6 — J_A − J_A T = J_{A⁻¹}T + J_{B⁻¹}R_A ∈ ran A + ran B and J_{A⁻¹} − J_{A⁻¹}T = J_A T − J_B R_A ∈ dom A − dom B
-- statement:
--   Let $X$ be a real Hilbert space, let $A, B : X \rightrightarrows X$ be maximally monotone with resolvents $J_A, J_B$, put $R_A = 2J_A - \mathrm{Id}$, $J_{A^{-1}} = \mathrm{Id} - J_A$, $J_{B^{-1}} = \mathrm{Id} - J_B$, and let $T = \mathrm{Id} - J_A + J_B R_A$ be the Douglas–Rachford operator. Then for every $x \in X$:
--
--   1. $$J_A x - J_A T x = J_{A^{-1}} T x + J_{B^{-1}} R_A x,$$ and this vector lies in $\operatorname{ran}A + \operatorname{ran}B$;
--   2. $$J_{A^{-1}} x - J_{A^{-1}} T x = J_A T x - J_B R_A x,$$ and this vector lies in $\operatorname{dom}A - \operatorname{dom}B$.
--
--   These identities locate the increments of the two shadow sequences in $R$ and $D$, which is how $v_R$ and $v_D$ enter the dynamics of $T$.
--
--   **Formalization Note** $J_A, J_B$ are maps characterized by $x - J_A x \in A(J_A x)$ (the published `IsResolvent 1`), and $J_{A^{-1}}$ is `resInv JA` $= \mathrm{Id} - J_A$ by the inverse resolvent identity (8). The lemma precedes the standing assumption (12), which is not assumed. `CompleteSpace X` makes the space Hilbert.
-- source:
--   Bauschke & Moursi, On the Douglas–Rachford algorithm for solving possibly inconsistent optimization problems, arXiv:2106.11547v1 (22 Jun 2021), p. 6, Lemma 2.2

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_InconsistentDR_Shadow_Operators

namespace InconsistentDR.Shadow

open scoped InnerProductSpace
open ThreeOpSplitting.Convergence

/-- Lemma 2.2, p. 6 (before the standing assumption (12)). With `T = drT JA JB`,
`J_{A⁻¹} = resInv JA` and `J_{B⁻¹} = resInv JB` (by (8)), for every `x`:
(i) `J_A x − J_A T x = J_{A⁻¹} T x + J_{B⁻¹} R_A x ∈ ran A + ran B`;
(ii) `J_{A⁻¹} x − J_{A⁻¹} T x = J_A T x − J_B R_A x ∈ dom A − dom B`. -/
theorem lemma_2_2 {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (A B : X → Set X) (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (JA JB : X → X) (hJA : IsResolvent 1 A JA) (hJB : IsResolvent 1 B JB) (x : X) :
    (JA x - JA (drT JA JB x) = resInv JA (drT JA JB x) + resInv JB (refl JA x) ∧
      JA x - JA (drT JA JB x) ∈ setR A B) ∧
    (resInv JA x - resInv JA (drT JA JB x) = JA (drT JA JB x) - JB (refl JA x) ∧
      resInv JA x - resInv JA (drT JA JB x) ∈ setD A B) := by sorry

end InconsistentDR.Shadow
