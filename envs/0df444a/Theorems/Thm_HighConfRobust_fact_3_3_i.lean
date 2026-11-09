-- Prove2me | Theorems.Thm_HighConfRobust_fact_3_3_i
-- name    : HighConfRobust.fact_3_3_i
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:06:48.454546+00:00
-- url     : https://prove2.me/theorems/9aca2ee6-2079-48a0-ae6a-c7938333c24b
-- title:
--   Fact 3.3 (i) — data processing inequality for Rényi divergence
-- statement:
--   For every order $q\ge 1$, all probability distributions $P,Q$ on $\mathcal X$ and every measurable randomized map $f$ (a Markov kernel from $\mathcal X$ to a measurable space $\mathcal Y$),
--
--   $$
--   D_q\big(f(P)\,\|\,f(Q)\big)\le D_q(P\,\|\,Q),
--   $$
--
--   where $f(P)$ is the distribution of the output of $f$ on an input $X\sim P$.
--
--   Processing data cannot increase the Rényi divergence; the proof of Theorem 4.2 applies it to the pre-processing map $f$.
--
--   **Formalization Note** The randomized map is a Markov kernel $\kappa$ and $f(P)$ is the composition $\kappa\circ P$; a deterministic measurable map is the deterministic kernel. $D_q$ is the mission's `renyiDivergence` (the KL divergence at $q=1$).
--
--   Differences from the source:
--   - encoding: measurable randomized map f, f(P) the law of f(X) for X ∼ P → Markov kernel κ : Kernel X Y into any measurable space Y, f(P) = κ ∘ₘ P; reason: a measurable randomized map is a Markov kernel; the page fixes no output space
-- source:
--   Narayanan–Lee–Pensia, High Confidence Yields Outlier Robustness, STOC 2027 submission manuscript, Nov. 3, 2026 (sha256 f0e4ec41…c370c153), Fact 3.3 (i), p.16

import Mathlib
import Definitions.Def_HighConfRobust_renyiDivergence

namespace HighConfRobust

open MeasureTheory ProbabilityTheory

/-- **Fact 3.3 (i)** (data processing inequality for Rényi divergence, p.16). For every order
`q ≥ 1`, every measurable randomized map (Markov kernel) `κ` and probability measures `P, Q`,
`D_q(κ(P) ‖ κ(Q)) ≤ D_q(P ‖ Q)`, where `κ(P)` is the law of the output of `κ` on an input `X ∼ P`.

Narayanan–Lee–Pensia, *High Confidence Yields Outlier Robustness: Consequences in Computational
Hardness, Privacy, and Replicability*, STOC 2027 submission manuscript, Nov. 3, 2026
(sha256 f0e4ec41…c370c153), Fact 3.3 (i), p.16.

**Formalization Note** A measurable randomized map from `X` to a measurable space `Y` is a Markov
kernel `κ : Kernel X Y`; `f(P)` is the composition `κ ∘ₘ P`. A measurable deterministic map `f` is
the kernel `Kernel.deterministic f hf`. `D_q` is `HighConfRobust.renyiDivergence` (KL at `q = 1`). -/
theorem fact_3_3_i {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (κ : Kernel X Y) [IsMarkovKernel κ] (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (q : ℝ) (hq : 1 ≤ q) :
    renyiDivergence q (κ ∘ₘ P) (κ ∘ₘ Q) ≤ renyiDivergence q P Q := by sorry

end HighConfRobust
