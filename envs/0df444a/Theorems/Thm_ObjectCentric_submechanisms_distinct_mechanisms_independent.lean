-- Prove2me | Theorems.Thm_ObjectCentric_submechanisms_distinct_mechanisms_independent
-- name    : ObjectCentric.submechanisms_distinct_mechanisms_independent
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-23T19:37:11.409883+00:00
-- url     : https://prove2.me/theorems/28507dfb-dc97-42f3-b42e-ba577338bf92
-- title:
--   Lemma 1: sub-mechanisms of distinct mechanisms are independent
-- statement:
--   Let $K\ge0$ and $M\ge1$, let $\mathcal Z=(\mathbb R^M)^K$ and let $\mathcal X\subseteq\mathbb R^N$. Let $\mathbf f:\mathcal Z\to\mathcal X$ be a diffeomorphism with inverse $\mathbf g$ that is compositional, and let $S_1,S_2\subseteq[N]$ be nonempty. Then for all $\mathbf z\in\mathcal Z$ and $k\in[K]$, if $S_1\subseteq I_k(\mathbf z)$ and $S_2\cap I_k(\mathbf z)=\emptyset$, the sub-mechanisms $\mathbf J\mathbf f_{S_1}(\mathbf z)$ and $\mathbf J\mathbf f_{S_2}(\mathbf z)$ are independent:
--
--   $$\operatorname{rank}\mathbf J\mathbf f_{S_1\cup S_2}(\mathbf z)=\operatorname{rank}\mathbf J\mathbf f_{S_1}(\mathbf z)+\operatorname{rank}\mathbf J\mathbf f_{S_2}(\mathbf z).$$
--
--   Pixels of one object and pixels outside it never share latent capacity.
--
--   **Formalization Note** The slot dimension is assumed to satisfy $M\ge1$, which the paper takes for granted (each slot encodes $M$ object properties). This statement does not need it: for $M=0$ every rank in it is $0$ and it still holds.
-- source:
--   Brady, Zimmermann, Sharma, Schölkopf, von Kügelgen and Brendel, Provably Learning Object-Centric Representations, ICML 2023, arXiv:2305.14229v1 (2023), Appendix A, Lemma 1, p. 15

import Mathlib
import Definitions.Def_ObjectCentric_Basic

open MeasureTheory

namespace ObjectCentric

theorem submechanisms_distinct_mechanisms_independent {K M N : ℕ} (hM : 0 < M)
    (X : Set (Obs N)) (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (hfc : IsCompositional f) (S₁ S₂ : Set (Fin N)) (h₁ : S₁.Nonempty) (h₂ : S₂.Nonempty) :
    ∀ (z : Lat K M) (k : Fin K), S₁ ⊆ indexSet f z k → S₂ ∩ indexSet f z k = ∅ →
      SubmechIndependent f z S₁ S₂ := by sorry

end ObjectCentric
