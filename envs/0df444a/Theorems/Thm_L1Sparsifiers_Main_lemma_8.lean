-- Prove2me | Theorems.Thm_L1Sparsifiers_Main_lemma_8
-- name    : L1Sparsifiers.Main.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:07:11.058546+00:00
-- url     : https://prove2.me/theorems/a291dff3-25e6-4f80-a5a4-62a5233df7cc
-- title:
--   Lemma 8 — tail bound $\mathbb P[\langle v,x\rangle>\sqrt\lambda\|v\|_2]\le2^{-2\lambda}$ for $x$ uniform on $[-1,1]^m$
-- statement:
--   Let $v\in\mathbb R^m$ and let $x$ be uniform on the solid cube $[-1,1]^m$. Then for every $\lambda\ge0$,
--   $$\mathbb P\Big[\langle v,x\rangle>\sqrt{\lambda}\,\|v\|_2\Big]\le2^{-2\lambda},$$
--   where $\|v\|_2=\big(\sum_i v_i^2\big)^{1/2}$. The cases $v=0$ and $\lambda=0$ are included.
--
--   This variant of Hoeffding's inequality is used in Lemma 24 to bound the volume cut from coordinate sections by halfspaces.
--
--   Differences from the source:
--   - encoding: P_{x∼[−1,1]^m}[⟨v,x⟩ > √λ‖v‖₂] → Vol_m(event ∩ [−1,1]^m)/2^m; reason: the event is an open halfspace (or empty), hence measurable
-- source:
--   Victor Reis, Thomas Rothvoss, Linear-size ℓ1 sparsifiers, STOC 2027 submission #162 (October 2026; PDF SHA-256 5137e7dee3cd303bd508f90f5f42c955632af5dc2ec978d9ef575bae4ce23710), §2, Lemma 8, p.6; proof in Appendix A, pp.25–26

import Mathlib
import Definitions.Def_L1Sparsifiers_Main_UniformCube

namespace L1Sparsifiers.Main

/-- **Lemma 8** (p.6; proof in Appendix A, pp.25–26). "Let v ∈ ℝ^m and x ∼ [−1,1]^m uniformly.
Then P[⟨v, x⟩ > √λ ‖v‖₂] ≤ 2^{−2λ} for any λ ≥ 0."

`‖v‖₂ = √(∑ᵢ vᵢ²)`; the tail event is strict; `v = 0` and `λ = 0` are included. -/
theorem lemma_8 {m : ℕ} (v : Fin m → ℝ) (lam : ℝ) (hlam : 0 ≤ lam) :
    cubeProb m {x | Real.sqrt lam * Real.sqrt (∑ i, v i ^ 2) < ∑ i, v i * x i} ≤
      (2 : ℝ) ^ (-2 * lam) := by sorry

end L1Sparsifiers.Main
