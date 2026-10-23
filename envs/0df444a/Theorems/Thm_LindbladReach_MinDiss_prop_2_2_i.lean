-- Prove2me | Theorems.Thm_LindbladReach_MinDiss_prop_2_2_i
-- name    : LindbladReach.MinDiss.prop_2_2_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:04:34.830988+00:00
-- url     : https://prove2.me/theorems/ee4f1674-848e-4190-b481-f53cb5748869
-- title:
--   Proposition 2.2(i), p. 5, as used — for a Hörmander system S, every unitary conjugation Ad_U is in the closed class Channel(S)
-- statement:
--   Let $H=\mathbb C^{2^k}$ and let $S$ be a set of operators on $H$ whose anti-Hermitian span generates a Hörmander system. Then every unitary conjugation channel belongs to the closed resource class:
--   $$\operatorname{Ad}_U\in\overline{\mathrm{Channel}(S)}\qquad\text{for every unitary }U\in U(2^k),\quad \operatorname{Ad}_U(\rho)=U\rho U^*.$$
--
--   The rule (UN) puts only the forward flows $\operatorname{Ad}_{e^{tX}}$, $t\ge0$, of the available anti-Hermitian directions $X$ into the class. This statement says that composition and closure then give every unitary channel. The paper's proof attributes it to Chow's theorem. The proofs of Lemma 2.11 and Theorem 2.12 use it to apply register swaps, local rotations and an arbitrary preparation unitary.
--
--   **Formalization Note** The page writes (i) as "$\operatorname{Ad}_{its}\in\mathrm{Channel}(S)$ if $s=s^*$ and $s\in\operatorname{span}(S)$". Read literally, that only restates (UN). Its proof (Chow's theorem) and all of its uses require every unitary $U$, and that is the form posed here. The page's hypothesis is only that $S$ is a Hörmander system, so $S=S^*$ is not assumed. Proposition 2.2 prints $\mathrm{Channel}(S)$ without the overline. Membership is posed in the closed class $\overline{\mathrm{Channel}(S)}$, because the proofs of (ii) and (iii) take Trotter limits and every use (Lemma 2.11, Theorem 2.12) is in the closed class.
-- source:
--   Cai, Govindarajan, Junge, How Far do Lindbladians Go?, arXiv:2504.04883v2, p. 5, Proposition 2.2(i) and its proof; uses in the proofs of Lemma 2.11 and Theorem 2.12, p. 8

import Mathlib
import Definitions.Def_LindbladReach_MinDiss_Setting

namespace LindbladReach.MinDiss

open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

/-- Proposition 2.2(i), p. 5, as its proof (Chow) and its uses read it: for a Hörmander system `S`,
every unitary conjugation `Ad_U` lies in the closed class. -/
theorem prop_2_2_i {k : ℕ} (S : Set (Mat k)) (hH : IsHormander S) :
    ∀ U ∈ Matrix.unitaryGroup (Idx k) ℂ, unitaryConj U ∈ channelClosure S := by sorry

end LindbladReach.MinDiss
