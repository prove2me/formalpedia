-- Prove2me | Theorems.Thm_ObjectCentric_inferred_slot_meets_one_object
-- name    : ObjectCentric.inferred_slot_meets_one_object
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-23T19:39:53.848205+00:00
-- url     : https://prove2.me/theorems/cfd46d77-3f05-43de-b56f-1d3d8cf15254
-- title:
--   Proposition 2: each inferred slot generates pixels of exactly one ground-truth slot
-- statement:
--   Let $K\ge0$ and $M\ge1$, let $\mathcal Z=(\mathbb R^M)^K$ and let $\mathcal X\subseteq\mathbb R^N$. Let $\mathbf f:\mathcal Z\to\mathcal X$ be a diffeomorphism with inverse $\mathbf g$ that is compositional with irreducible mechanisms. Let $\hat{\mathbf g}:\mathcal X\to\mathcal Z$ be a diffeomorphism with inverse $\hat{\mathbf f}:\mathcal Z\to\mathcal X$ that is compositional. Write $\hat{\mathbf z}=\hat{\mathbf g}(\mathbf f(\mathbf z))$ and let $\hat I_j(\hat{\mathbf z})$ be the index sets of $\hat{\mathbf f}$. Then for all $\mathbf z\in\mathcal Z$ and $j\in[K]$ there is exactly one $i\in[K]$ with
--
--   $$\hat I_j(\hat{\mathbf z})\cap I_i(\mathbf z)\neq\emptyset.$$
--
--   Each inferred slot generates pixels of exactly one ground-truth slot.
--
--   **Formalization Note** The slot dimension is assumed to satisfy $M\ge1$, which the paper takes for granted (each slot encodes $M$ object properties).
-- source:
--   Brady, Zimmermann, Sharma, Schölkopf, von Kügelgen and Brendel, Provably Learning Object-Centric Representations, ICML 2023, arXiv:2305.14229v1 (2023), Appendix A, Proposition 2, pp. 16-18

import Mathlib
import Definitions.Def_ObjectCentric_Basic

open MeasureTheory

namespace ObjectCentric

theorem inferred_slot_meets_one_object {K M N : ℕ} (hM : 0 < M) (X : Set (Obs N))
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (hfc : IsCompositional f) (hfi : IsIrreducible f)
    (ghat : Obs N → Lat K M) (fhat : Lat K M → Obs N) (hhat : IsDiffeoWithInv fhat ghat X)
    (hfhatc : IsCompositional fhat) :
    ∀ (z : Lat K M) (j : Fin K), ∃! i : Fin K,
      (indexSet fhat (ghat (f z)) j ∩ indexSet f z i).Nonempty := by sorry

end ObjectCentric
