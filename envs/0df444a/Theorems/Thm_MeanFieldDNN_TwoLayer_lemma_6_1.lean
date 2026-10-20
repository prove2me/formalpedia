-- Prove2me | Theorems.Thm_MeanFieldDNN_TwoLayer_lemma_6_1
-- name    : MeanFieldDNN.TwoLayer.lemma_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:24:44.789743+00:00
-- url     : https://prove2.me/theorems/1495b375-35b3-41b4-b1d3-65cdd25ce2ed
-- title:
--   Lemma 6.1 — uniqueness of the limiting system
-- statement:
--   Any two continuous solutions of (2.6) have identical output-weight, first-layer, and second-layer paths for every $t\in[0,1]$ and all initial values in their respective compact supports:
--
--   $$(\widetilde C,\widetilde W^1,\widetilde W^2)=(\overline C,\overline W^1,\overline W^2).$$
--
--   Thus the limiting output $g_t(x)$ does not depend on a choice of solution. This is the uniqueness clause of Theorem 2.3.
--
--   **Formalization Note** Equality is asserted on the source's continuous-solution domain, the initial support sets.
-- source:
--   Sirignano, Spiliopoulos, Mean Field Analysis of Deep Neural Networks, arXiv:1903.04440v5, p. 25, Lemma 6.1

import Mathlib
import Definitions.Def_MeanFieldDNN_TwoLayer_Model

open MeasureTheory Filter Set
open scoped InnerProductSpace ENNReal

noncomputable section

namespace MeanFieldDNN.TwoLayer

theorem lemma_6_1 {d : ℕ} (S : Setting d)
    (L R : LimitPaths d) (hL : IsLimitSolution S L) (hR : IsLimitSolution S R) :
    (∀ t ∈ Icc (0 : ℝ) 1, ∀ c ∈ S.Cset, L.Ct t c = R.Ct t c) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ S.W1set, L.W1t t w = R.W1t t w) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, ∀ c ∈ S.Cset, ∀ w ∈ S.W1set,
      ∀ u ∈ S.W2set, L.W2t t c w u = R.W2t t c w u) := by sorry
end MeanFieldDNN.TwoLayer
