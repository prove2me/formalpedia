-- Prove2me | Theorems.Thm_HolevoCQ_sec6_bounds
-- name    : HolevoCQ.sec6_bounds
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:17:36.927245+00:00
-- url     : https://prove2.me/theorems/619d21af-5a20-4fe9-8006-0b514a147c86
-- title:
--   §6: $\mathsf MS_u=\bar S^{\otimes n}$, $\|P\bar S^{\otimes n}P\|\le2^{-n[H(\bar S)-\delta]}$, $\mathrm{Tr}P_u\le\mathrm{Tr}S_u2^{n[\bar H+\delta]}$
-- statement:
--   Let $\pi$ be a distribution on the finite alphabet $A$, $\delta>0$, $n\ge0$, and let words $u\in A^n$ be drawn from the product law (9). With $P$ the typical projector (6) and $P_u$ the typical projector (8):
--
--   1. $\mathsf MS_u=\bar S^{\otimes n}$;
--   2. $\|P\bar S^{\otimes n}P\|\le2^{-n[H(\bar S)-\delta]}$;
--   3. for every word $u$, $\mathrm{Tr}\,P_u\le\mathrm{Tr}\,S_u\cdot2^{n[\bar H(S_{(\cdot)})+\delta]}$, where $\bar H(S_{(\cdot)})=\sum_i\pi_iH(S_i)$; hence
--
--   $$
--   \mathrm{Tr}\,\mathsf MP_{u'}=\mathsf M\,\mathrm{Tr}\,P_{u'}\le\mathsf M\,\mathrm{Tr}\,S_{u'}\cdot2^{n[\bar H(S_{(\cdot)})+\delta]}=2^{n[\bar H(S_{(\cdot)})+\delta]} .
--   $$
--
--   These three facts turn the error bound (17) into the random-coding bound (18).
--
--   Differences from the source:
--   - encoding: input alphabet $A=\{1,\dots,a\}$, $D=\{1,\dots,d\}$, $\mathcal H=\mathbb C^d$, $\mathcal H^{\otimes n}$ → arbitrary finite types `A`, `D`; $\mathcal H=\mathbb C^D$; $\mathcal H^{\otimes n}=\mathbb C^{D^n}$ indexed by `Fin n → D`; reason: Lean convention; every finite alphabet is in bijection with some finite type and conversely, so the instances are the same
--   - encoding: the alphabet $A$ is not said to be nonempty → `[Nonempty A]`; reason: with $A$ empty there is no probability distribution on $A$, so $C_n$ and $\max_\pi$ are undefined; the hypothesis excludes only that undefined case
--   - encoding: expectation $\mathsf M$ over words drawn from the law (9) → finite sum over `u : Fin n → A` weighted by `wordProb π n u`; reason: the law (9) is a finite probability vector, so the expectation is this finite sum
--   - encoding: $P=\sum_{J\in B}|e_J\rangle\langle e_J|$, a sum over an eigenbasis with eigenvalue in the open window → `cfc` of the indicator of the open interval (`windowProj`); reason: for a Hermitian matrix this equals the sum of eigenprojectors with eigenvalue in the open window, for every choice of eigenbasis
--   - encoding: operator norm bound $\|P\bar S^{\otimes n}P\|\le c$ → Loewner bound $c\,I-P\bar S^{\otimes n}P\succeq0$; reason: equivalent for the positive operator $P\bar S^{\otimes n}P$
--   - generalization: $\mathsf M\,\mathrm{Tr}\,P_{u'}\le\mathsf M\,\mathrm{Tr}\,S_{u'}\cdot2^{n[\bar H+\delta]}$ (in expectation) → $\mathrm{Tr}\,P_u\le\mathrm{Tr}\,S_u\cdot2^{n[\bar H+\delta]}$ for every word $u$; reason: averaging the pointwise inequality with the law (9) gives the printed one, and $\mathrm{Tr}\,S_u=1$ gives the final equality
--   - encoding: traces $\mathrm{Tr}$ of operators → real part of the matrix trace; reason: the traces involved are real
-- source:
--   Holevo, The Capacity of Quantum Channel with General Signal States, arXiv:quant-ph/9611023v1, §6, p.6

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_HolevoCQ_tensorPowMat
import Definitions.Def_HolevoCQ_wordState
import Definitions.Def_HolevoCQ_wordProb
import Definitions.Def_HolevoCQ_avgState
import Definitions.Def_HolevoCQ_typProj
import Definitions.Def_HolevoCQ_condTypProj

open QAlgorithms
open scoped ComplexOrder

namespace HolevoCQ

/-- Holevo, *The Capacity of Quantum Channel with General Signal States*,
arXiv:quant-ph/9611023v1, §6, p.6: with words drawn from the product law (9),
(a) `M S_u = S̄^{⊗n}`;
(b) by the definition of `P`, `‖P S̄^{⊗n} P‖ ≤ 2^{−n[H(S̄)−δ]}`;
(c) by the definition of `P_u`, `Tr P_u ≤ Tr S_u · 2^{n[H̄(S(·))+δ]}`, whence
`Tr M P_{u'} = M Tr P_{u'} ≤ M Tr S_{u'} · 2^{n[H̄(S(·))+δ]} = 2^{n[H̄(S(·))+δ]}`.

**Formalization Note.** (a) is the finite sum over words weighted by `wordProb`. In (b) the
operator norm bound is written as the Loewner bound `P S̄^{⊗n} P ≤ c · I`, equivalent for the
positive operator `P S̄^{⊗n} P`. (c) is stated for every word `u` (the pointwise inequality
behind the printed expectation). `H` is the binary `vnEntropy`; `2^x` is `Real.rpow`. -/
theorem sec6_bounds {A D : Type} [Fintype A] [DecidableEq A] [Nonempty A] [Fintype D]
    [DecidableEq D] (S : A → Matrix D D ℂ) (hS : ∀ i, IsDensityMatrix (S i)) (π : A → ℝ)
    (hπ : π ∈ stdSimplex ℝ A) (δ : ℝ) (hδ : 0 < δ) (n : ℕ) :
    (∑ u : Fin n → A, ((wordProb π n u : ℝ) : ℂ) • wordState S n u =
        tensorPowMat (avgState S π) n) ∧
      ((((2 : ℝ) ^ (-((n : ℝ) * (vnEntropy (avgState S π) - δ))) : ℝ) : ℂ) • 1 -
          typProj S π n δ * tensorPowMat (avgState S π) n * typProj S π n δ).PosSemidef ∧
      ∀ u : Fin n → A, (condTypProj S π n δ u).trace.re ≤
        (wordState S n u).trace.re * (2 : ℝ) ^ ((n : ℝ) * (∑ i, π i * vnEntropy (S i) + δ)) := by sorry

end HolevoCQ
