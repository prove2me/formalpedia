-- Prove2me | Theorems.Thm_MeanFieldDNN_TwoLayer_first_layer_limit
-- name    : MeanFieldDNN.TwoLayer.first_layer_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:24:41.635896+00:00
-- url     : https://prove2.me/theorems/4576fccf-5723-48e8-a9f6-590005b66a90
-- title:
--   §2 consequence of Lemma 2.2 — first-layer output limit
-- statement:
--   Fix $N_2\ge1$, $t\in[0,1]$, and $x$ in the input support $X$. Under Assumption 2.1, as $N_1\to\infty$ the output after $\lfloor N_1t\rfloor$ SGD steps converges in probability to the output of the $N_2$-particle system:
--
--   $$g_t^{N_1,N_2}(x)\xrightarrow[N_1\to\infty]{\mathbb P}g_t^{N_2}(x).$$
--
--   This is the first limit in Theorem 2.3's iterated limit. The random initial output weights are shared by the network and the particle system.
--
--   **Formalization Note** All widths and particles are coupled on one probability space. The source states this consequence immediately after Lemma 2.2.
-- source:
--   Sirignano, Spiliopoulos, Mean Field Analysis of Deep Neural Networks, arXiv:1903.04440v5, p. 5, unnumbered consequence immediately after Lemma 2.2

import Mathlib
import Definitions.Def_MeanFieldDNN_TwoLayer_Model

open MeasureTheory Filter Set
open scoped InnerProductSpace ENNReal

noncomputable section

namespace MeanFieldDNN.TwoLayer

theorem first_layer_limit {d : ℕ} (S : Setting d)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (C0 : Ω → ℕ → ℝ) (W20 : Ω → ℕ → ℕ → ℝ)
    (W10 : Ω → ℕ → E d) (dat : Ω → ℕ → E d × ℝ)
    (hInit : IsInitLaw S P C0 W20 W10 dat)
    (N2 : ℕ) (hN2 : 1 ≤ N2) (Q : ParticlePaths d N2)
    (hQ : IsParticleSolution S N2 Q) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (x : E d) (hx : x ∈ S.X) :
    TendstoInMeasure P
      (fun N1 (ω : Ω) => gNN S N1 N2 t x (C0 ω) (W20 ω) (W10 ω) (dat ω))
      atTop (fun ω => partG S Q t (fun i => C0 ω i.val) x) := by sorry
end MeanFieldDNN.TwoLayer
