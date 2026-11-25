-- Prove2me | Theorems.Thm_ObjectCentric_object_meets_one_inferred_slot
-- name    : ObjectCentric.object_meets_one_inferred_slot
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-23T19:40:48.767308+00:00
-- url     : https://prove2.me/theorems/86fe06ef-d8cf-48b9-bf20-ce11c04c183b
-- title:
--   Corollary 1: each ground-truth slot generates pixels of exactly one inferred slot
-- statement:
--   Under the hypotheses of Proposition 2: Let $K\ge0$ and $M\ge1$, let $\mathcal Z=(\mathbb R^M)^K$ and let $\mathcal X\subseteq\mathbb R^N$. Let $\mathbf f:\mathcal Z\to\mathcal X$ be a diffeomorphism with inverse $\mathbf g$ that is compositional with irreducible mechanisms. Let $\hat{\mathbf g}:\mathcal X\to\mathcal Z$ be a diffeomorphism with inverse $\hat{\mathbf f}:\mathcal Z\to\mathcal X$ that is compositional. Write $\hat{\mathbf z}=\hat{\mathbf g}(\mathbf f(\mathbf z))$ and let $\hat I_j(\hat{\mathbf z})$ be the index sets of $\hat{\mathbf f}$. Then for all $\mathbf z\in\mathcal Z$ and $i\in[K]$ there is exactly one $j\in[K]$ with
--
--   $$\hat I_j(\hat{\mathbf z})\cap I_i(\mathbf z)\neq\emptyset.$$
--
--   **Formalization Note** The paper states the corollary without repeating hypotheses. They are those of Proposition 2, which it applies, and they are written out here. The slot dimension is assumed to satisfy $M\ge1$.
-- source:
--   Brady, Zimmermann, Sharma, Schölkopf, von Kügelgen and Brendel, Provably Learning Object-Centric Representations, ICML 2023, arXiv:2305.14229v1 (2023), Appendix A, Corollary 1, p. 18

import Mathlib
import Definitions.Def_ObjectCentric_Basic

open MeasureTheory

namespace ObjectCentric

theorem object_meets_one_inferred_slot {K M N : ℕ} (hM : 0 < M) (X : Set (Obs N))
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (hfc : IsCompositional f) (hfi : IsIrreducible f)
    (ghat : Obs N → Lat K M) (fhat : Lat K M → Obs N) (hhat : IsDiffeoWithInv fhat ghat X)
    (hfhatc : IsCompositional fhat) :
    ∀ (z : Lat K M) (i : Fin K), ∃! j : Fin K,
      (indexSet fhat (ghat (f z)) j ∩ indexSet f z i).Nonempty := by sorry

end ObjectCentric
