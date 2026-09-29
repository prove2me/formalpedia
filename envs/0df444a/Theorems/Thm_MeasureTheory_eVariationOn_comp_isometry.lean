-- Prove2me | Theorems.Thm_MeasureTheory_eVariationOn_comp_isometry
-- name    : MeasureTheory.eVariationOn_comp_isometry
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T07:34:41.531134+00:00
-- url     : https://prove2.me/theorems/84297440-01b6-4489-8f94-44f1de2373bd
-- title:
--   The variation of a curve is unchanged by an isometry of the target
-- statement:
--   If $f$ is an isometry, then for every curve $g$ and every parameter set $s$,
--   $$V_s(f\circ g)=V_s(g).$$
--   That is, the total variation — the length of a curve — is an invariant of the target up to isometry.
--
--   **Role.** Lengths of curves in a metric space should not depend on how the space is presented, and in particular a curve lying in an apartment of a Euclidean building has the same length computed in the building or in the model apartment through a chart. That is exactly what is needed to compute the length of the image of a circle under a harmonic map by transporting it into the model space, where it is a great circle arc.
--
--   **The argument.** The variation is the supremum, over finite increasing families of parameters, of the sums of distances between consecutive values. An isometry leaves each such distance unchanged, so the two suprema range over identical families of identical numbers.
--
--   **Formalization note.** Only the isometry property is used; $f$ need not be surjective, so the statement applies to isometric embeddings such as apartment charts.
-- source:
--   Standard; the invariance of the length of a curve under an isometry of the target, used to compute lengths inside an apartment in C. Breiner and B. K. Dees, arXiv:2604.16608, Lemma 3.2.

import Mathlib

namespace MeasureTheory

universe u v w

theorem eVariationOn_comp_isometry {α : Type u} [LinearOrder α] {E : Type v}
    [PseudoEMetricSpace E] {F : Type w} [PseudoEMetricSpace F] (f : E → F)
    (hf : Isometry f) (g : α → E) (s : Set α) :
    eVariationOn (f ∘ g) s = eVariationOn g s := by sorry

end MeasureTheory
