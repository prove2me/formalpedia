-- Prove2me | Theorems.Thm_MeanFieldDNN_TwoLayer_lemma_A_5
-- name    : MeanFieldDNN.TwoLayer.lemma_A_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:24:47.10418+00:00
-- url     : https://prove2.me/theorems/aa57649f-ee48-4d86-8e75-502a74478de6
-- title:
--   Lemma A.5 — well-posedness of the finite particle system
-- statement:
--   For every positive second-layer width $N_2$, the finite particle system (5.1) has a solution. Any two solutions agree for all $t\in[0,1]$ and for every initial value in the compact product supports.
--
--   $$\exists Q\;\mathrm{Sol}_{N_2}(Q),\qquad \mathrm{Sol}_{N_2}(Q)\land\mathrm{Sol}_{N_2}(R)\Longrightarrow Q=R\text{ on supported initial states}.$$
--
--   This establishes that the intermediate network output $g_t^{N_2}$ is well defined.
--
--   **Formalization Note** The paper states Lemma A.5 for its measure evolution equation (A.4). Its proof identifies that equation with the particle system (A.6), which is (5.1); the theorem records well-posedness in this particle form.
-- source:
--   Sirignano, Spiliopoulos, Mean Field Analysis of Deep Neural Networks, arXiv:1903.04440v5, p. 31, Lemma A.5; p. 32, (A.6)

import Mathlib
import Definitions.Def_MeanFieldDNN_TwoLayer_Model

open MeasureTheory Filter Set
open scoped InnerProductSpace ENNReal

noncomputable section

namespace MeanFieldDNN.TwoLayer

theorem lemma_A_5 {d : ℕ} (S : Setting d) (N2 : ℕ) (hN2 : 1 ≤ N2) :
    (∃ Q : ParticlePaths d N2, IsParticleSolution S N2 Q) ∧
    (∀ Q R : ParticlePaths d N2, IsParticleSolution S N2 Q → IsParticleSolution S N2 R →
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ cv : Fin N2 → ℝ, (∀ i, cv i ∈ S.Cset) →
        ∀ i, Q.Cp t cv i = R.Cp t cv i) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ cv : Fin N2 → ℝ, (∀ i, cv i ∈ S.Cset) →
        ∀ w ∈ S.W1set, ∀ uv : Fin N2 → ℝ, (∀ i, uv i ∈ S.W2set) →
          Q.W1p t cv w uv = R.W1p t cv w uv) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ cv : Fin N2 → ℝ, (∀ i, cv i ∈ S.Cset) →
        ∀ w ∈ S.W1set, ∀ uv : Fin N2 → ℝ, (∀ i, uv i ∈ S.W2set) →
          ∀ i, Q.W2p t cv i w uv = R.W2p t cv i w uv)) := by sorry
end MeanFieldDNN.TwoLayer
