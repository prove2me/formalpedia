-- Prove2me | Theorems.Thm_JainCRERepetition_Cubic_lemma_4_1
-- name    : JainCRERepetition.Cubic.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:12:06.326985+00:00
-- url     : https://prove2.me/theorems/547bb1aa-e90e-4a04-9d37-e855665cfc66
-- title:
--   Lemma 4.1 — local preparation and pure descriptions
-- statement:
--   There is one universal sampler constant $C_{\rm sm}\ge1$ for which the following holds for every copied-input family with conditional comparisons and finite full divergences. Write $s=b_A+b_B$ and $C_{\rm prep}=100C_{\rm sm}$. Then
--
--   $$d_{\rm prep}(q,\psi)\le\min\{1,C_{\rm prep}\sqrt s\}.$$
--
--   Every positive slack has a finite-resource witness on the entire designated original workspace. After common finite pure padding, there are bipartite unit descriptions $u_x,v_y$, Alice isometries $J_x$ and Bob unitaries $W_y$ such that
--
--   $$\mathbb E_q\|u_x-v_y\|_2^2\le4(\ln2)(b_A+b_B),\qquad\mathbb E_qP^2((J_x\otimes W_y^\dagger)u_x(J_x^\dagger\otimes W_y),\psi_{xy})\le(\ln2)b_A.$$
--
--   All choices precede the questions; the respective maps use only the respective local questions. The paper's $O(\sqrt s)$ preparation dependence has explicit coefficient $100C_{\rm sm}$ in its proof on p. 28. No numerical sampler constant is invented.
--
--   Differences from the source:
--   - encoding: finite complex systems with support-aware binary relative entropy → complex matrices on finite bases; FiniteD guards real divergence differences; reason: kernel containment is the finite-divergence condition; no infinite divergence is converted to zero
--   - encoding: common finite pure padding and a fixed universal sampler constant → explicit tensor padding with zero ancillas; one existential Csm carrying the sampler property before all families; reason: basis identifications preserve the source isometries and keep the same constant for every dimension and input family
-- source:
--   Rahul Jain, Parallel Repetition for Entangled Games via Conditional Relative Entropy, STOC 2027 submission #1639 (October 2026), p. 27, Lemma 4.1, Eqs. (37)–(38); pinned PDF sha256 feaaea94c75228982a63b6750208082f2569d2e250a47abe4bf95fa37cc76a35

import Definitions.Def_JainCRERepetition_Cubic_copied

open scoped BigOperators Kronecker
open Matrix
noncomputable section

namespace JainCRERepetition.Cubic
attribute [local instance] Classical.propDecidable

theorem lemma_4_1 :
    ∃ Csm : ℝ, 1 ≤ Csm ∧ SamplingConstant Csm ∧
      ∀ (X Y A B : Type) [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
        [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]
        (F : CopiedFamily X Y A B)
        (νA : Op (AliceIndex X Y A)) (νB : Op (AliceIndex Y X B)),
        IsComparison F.prior νA → IsComparison F.flip.prior νB →
        FiniteD (aliceTarget F) νA → FiniteD (aliceTarget F.flip) νB →
        let s := bAlice F νA + bBob F νB
        let bound := min 1 (100*Csm*Real.sqrt s)
        dprep F.posterior.p F.vector ≤ bound ∧
        (∀ ζ : ℝ, 0 < ζ → ∃ P : Preparation (X := X) (Y := Y) (A := A) (B := B),
          preparationError F.posterior.p F.vector P ≤ bound + ζ) ∧
        PureDescriptions F νA νB := by sorry
end JainCRERepetition.Cubic
