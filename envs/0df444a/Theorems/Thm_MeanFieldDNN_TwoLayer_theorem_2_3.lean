-- Prove2me | Theorems.Thm_MeanFieldDNN_TwoLayer_theorem_2_3
-- name    : MeanFieldDNN.TwoLayer.theorem_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:24:57.572975+00:00
-- url     : https://prove2.me/theorems/480a6bc4-8a05-4692-98aa-b8e48ea6fe5d
-- title:
--   Theorem 2.3 — iterated mean-field limit and $N_2^{-1/2}$ rate
-- statement:
--   For the two-hidden-layer network (1.1) trained by SGD (1.4) under Assumption 2.1 and the learning rates (2.1), the limiting system (2.6) has a unique continuous solution. Its output is $g_t(x)$. For each $t\in[0,1]$ and $x\in X$,
--
--   $$\lim_{N_2\to\infty}\lim_{N_1\to\infty}g_t^{N_1,N_2}(x)=g_t(x)\quad\text{in probability},$$
--
--   and, for a constant $K$ independent of $N_2$, $t$, and $x$,
--
--   $$\mathbb E[|g_t^{N_2}(x)-g_t(x)|]\le K/\sqrt{N_2}.$$
--
--   The theorem identifies the output produced by the actual SGD iterates as the widths grow in order, and quantifies the error of the intermediate particle system.
--
--   **Formalization Note** The inner probability limit uses a limsup, implying the footnote's form whenever its inner limit exists. All widths share one product-law coupling. Existence is explicit, so the convergence clauses cannot hold vacuously. The rate constant is uniform over $t\in[0,1]$.
-- source:
--   Sirignano, Spiliopoulos, Mean Field Analysis of Deep Neural Networks, arXiv:1903.04440v5, pp. 5–6, Theorem 2.3

import Mathlib
import Definitions.Def_MeanFieldDNN_TwoLayer_Model

open MeasureTheory Filter Set Topology
open scoped InnerProductSpace ENNReal

noncomputable section

namespace MeanFieldDNN.TwoLayer

theorem theorem_2_3 {d : ℕ} (S : Setting d)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (C0 : Ω → ℕ → ℝ) (W20 : Ω → ℕ → ℕ → ℝ)
    (W10 : Ω → ℕ → E d) (dat : Ω → ℕ → E d × ℝ)
    (hInit : IsInitLaw S P C0 W20 W10 dat) :
    (∃ L : LimitPaths d, IsLimitSolution S L) ∧
    (∀ L R : LimitPaths d, IsLimitSolution S L → IsLimitSolution S R →
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ c ∈ S.Cset, L.Ct t c = R.Ct t c) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ S.W1set, L.W1t t w = R.W1t t w) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ c ∈ S.Cset, ∀ w ∈ S.W1set,
        ∀ u ∈ S.W2set, L.W2t t c w u = R.W2t t c w u)) ∧
    (∀ L : LimitPaths d, IsLimitSolution S L →
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ S.X, ∀ ε : ℝ, 0 < ε →
      Tendsto
        (fun N2 : ℕ => Filter.limsup
          (fun N1 : ℕ => P {ω : Ω |
            ε < |gNN S N1 N2 t x (C0 ω) (W20 ω) (W10 ω) (dat ω) - limG S L t x|})
          atTop) atTop (𝓝 0)) ∧
    (∀ L : LimitPaths d, IsLimitSolution S L →
      ∃ K : ℝ, ∀ (N2 : ℕ), 1 ≤ N2 → ∀ Q : ParticlePaths d N2,
        IsParticleSolution S N2 Q → ∀ t ∈ Icc (0 : ℝ) 1,
        ∀ x ∈ S.X,
          (∫ cv : Fin N2 → ℝ, |partG S Q t cv x - limG S L t x|
            ∂(Measure.pi fun _ : Fin N2 => S.μc)) ≤ K / Real.sqrt (N2 : ℝ)) := by sorry
end MeanFieldDNN.TwoLayer
