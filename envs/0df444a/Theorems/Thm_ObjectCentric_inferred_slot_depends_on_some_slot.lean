-- Prove2me | Theorems.Thm_ObjectCentric_inferred_slot_depends_on_some_slot
-- name    : ObjectCentric.inferred_slot_depends_on_some_slot
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-23T19:39:10.555784+00:00
-- url     : https://prove2.me/theorems/54cc348d-c9f2-406a-b808-29dc0c209c9b
-- title:
--   Proposition 1: every ground-truth slot affects some inferred slot
-- statement:
--   Let $K\ge0$ and $M\ge1$, let $\mathcal Z=(\mathbb R^M)^K$ and let $\mathcal X\subseteq\mathbb R^N$. Let $\mathbf f:\mathcal Z\to\mathcal X$ be a diffeomorphism with inverse $\mathbf g$ that is compositional. Let $\hat{\mathbf g}:\mathcal X\to\mathcal Z$ be a diffeomorphism (with inverse $\hat{\mathbf f}$) and $\hat{\mathbf z}:=\hat{\mathbf g}(\mathbf f(\mathbf z))$. Then for all $\mathbf z\in\mathcal Z$ and $i\in[K]$ there is $j\in[K]$ with
--
--   $$\frac{\partial\hat{\mathbf z}_j}{\partial\mathbf z_i}(\mathbf z)\neq\mathbf 0.$$
--
--   **Formalization Note** The slot dimension is assumed to satisfy $M\ge1$, which the paper takes for granted. For $M=0$ every block is the empty matrix and the statement would fail. The compositionality of $\mathbf f$ is a hypothesis of the paper's statement although its proof does not use it; it is kept.
-- source:
--   Brady, Zimmermann, Sharma, Schölkopf, von Kügelgen and Brendel, Provably Learning Object-Centric Representations, ICML 2023, arXiv:2305.14229v1 (2023), Appendix A, Proposition 1, p. 16

import Mathlib
import Definitions.Def_ObjectCentric_Basic

open MeasureTheory

namespace ObjectCentric

theorem inferred_slot_depends_on_some_slot {K M N : ℕ} (hM : 0 < M) (X : Set (Obs N))
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (hfc : IsCompositional f)
    (ghat : Obs N → Lat K M) (fhat : Lat K M → Obs N) (hhat : IsDiffeoWithInv fhat ghat X) :
    ∀ (z : Lat K M) (i : Fin K), ∃ j : Fin K, slotBlock (fun w => ghat (f w)) z j i ≠ 0 := by sorry

end ObjectCentric
