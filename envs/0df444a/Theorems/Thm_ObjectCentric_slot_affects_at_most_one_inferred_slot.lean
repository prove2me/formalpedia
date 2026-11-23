-- Prove2me | Theorems.Thm_ObjectCentric_slot_affects_at_most_one_inferred_slot
-- name    : ObjectCentric.slot_affects_at_most_one_inferred_slot
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T19:41:15.61989+00:00
-- url     : https://prove2.me/theorems/3f0083c5-701d-47e0-ad45-e386e22cf6e7
-- title:
--   Proposition 3: every ground-truth slot affects at most one inferred slot
-- statement:
--   Let $K\ge0$ and $M\ge1$, let $\mathcal Z=(\mathbb R^M)^K$ and let $\mathcal X\subseteq\mathbb R^N$. Let $\mathbf f:\mathcal Z\to\mathcal X$ be a diffeomorphism with inverse $\mathbf g$ that is compositional with irreducible mechanisms. Let $\hat{\mathbf g}:\mathcal X\to\mathcal Z$ be a diffeomorphism with inverse $\hat{\mathbf f}:\mathcal Z\to\mathcal X$ that is compositional. Write $\hat{\mathbf z}=\hat{\mathbf g}(\mathbf f(\mathbf z))$ and let $\hat I_j(\hat{\mathbf z})$ be the index sets of $\hat{\mathbf f}$. Then for all $\mathbf z\in\mathcal Z$ and $i\in[K]$ there is at most one $j\in[K]$ with
--
--   $$\frac{\partial\hat{\mathbf z}_j}{\partial\mathbf z_i}(\mathbf z)\neq\mathbf 0.$$
--
--   **Formalization Note** The slot dimension is assumed to satisfy $M\ge1$, which the paper takes for granted (each slot encodes $M$ object properties).
-- source:
--   Brady, Zimmermann, Sharma, Schölkopf, von Kügelgen and Brendel, Provably Learning Object-Centric Representations, ICML 2023, arXiv:2305.14229v1 (2023), Appendix A, Proposition 3, pp. 19-20

import Mathlib
import Definitions.Def_ObjectCentric_Basic

open MeasureTheory

namespace ObjectCentric

theorem slot_affects_at_most_one_inferred_slot {K M N : ℕ} (hM : 0 < M) (X : Set (Obs N))
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (hfc : IsCompositional f) (hfi : IsIrreducible f)
    (ghat : Obs N → Lat K M) (fhat : Lat K M → Obs N) (hhat : IsDiffeoWithInv fhat ghat X)
    (hfhatc : IsCompositional fhat) :
    ∀ (z : Lat K M) (i j j' : Fin K), slotBlock (fun w => ghat (f w)) z j i ≠ 0 →
      slotBlock (fun w => ghat (f w)) z j' i ≠ 0 → j = j' := by sorry

end ObjectCentric
