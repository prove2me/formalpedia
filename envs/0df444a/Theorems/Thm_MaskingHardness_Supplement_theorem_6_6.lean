-- Prove2me | Theorems.Thm_MaskingHardness_Supplement_theorem_6_6
-- name    : MaskingHardness.Supplement.theorem_6_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:38:24.902974+00:00
-- url     : https://prove2.me/theorems/f9241940-986a-4dd5-bc65-2184d27073b4
-- title:
--   Theorem 6.6 — universal masking channels: common post-processing
-- statement:
--   For every number of labels $k$:
--
--   1. there is a single map $\widehat W:\Delta_k\to\Delta_k^k$ that is a highest-fidelity response (Definition 1.18) for **every** monotone fidelity function $h$ simultaneously;
--   2. there is a (different) single map $\widehat W:\Delta_k\to\Delta_k^k$ that is a highest-fidelity response for **every** monotone mixing fidelity function $h$ simultaneously (Definition 1.19).
--
--   Being a highest-fidelity response means that at every $z\in\Delta_k$ the matrix $\widehat W(z)$ lies in $\Delta_k^k$, satisfies $\widehat W(z)z=\vec1/k$, and maximizes $\mathbb E_{y\sim z}[h(y,Wy)]$ among all such matrices. For these classes the masking channel post-processing a universal model can therefore be chosen independently of $h$.
--
--   **Formalization Note** The quantifiers are "there is $\widehat W$ such that for all $h$". The response is exact ($\gamma=0$ in `IsHighestFidelityResponse`). The claim is made for every $h$ of the form of Definition 1.19, whether or not $h$ is closed, proper and concave.
--
--   Differences from the source:
--   - generalization: for all monotone (resp. monotone mixing) fidelity functions h (closed, proper, concave, Definition 1.5) → for all h : Fin k → (Fin k → ℝ) → EReal of the Definition 1.19 form with h0 : ℝ → EReal nondecreasing (IsMonotoneFidelity / IsMonotoneMixingFidelity), with no closedness, properness or concavity; reason: every monotone (mixing) fidelity function is of this form, so the Lean statement specializes to the source; the proof only uses monotonicity of h0 and the effective domain
--   - encoding: a (best-)fidelity response, Ŵ_h(z) ∈ argmax (Definition 1.18) → IsHighestFidelityResponse h 0 Ŵ: feasible at every z ∈ Δ_k and sup ≤ fidelity of Ŵ(z); reason: for a feasible Ŵ(z) the supremum bound with γ = 0 is attainment of the maximum
--   - reading: h(y, z) = h0(µ) if z = µy + (1 − µ)1⃗/k for some µ ∈ [0, 1] → h(e_i, z) = h0(µ) for every µ ∈ [0, 1] with z = µe_i + (1 − µ)1⃗/k; reason: for k ≥ 2 the µ is unique; for k = 1 the source formula is only well defined if h0 is constant on [0, 1], which the Lean reading imposes
--   - encoding: Ŵ : Δ_k → Δ_k^k → a function (Fin k → ℝ) → Matrix (Fin k) (Fin k) ℝ constrained at every z ∈ Δ_k; reason: values off Δ_k are never used
-- source:
--   Gopalan–Prabhakaran–Tankala, Universal Hardness From Masking Channels, arXiv:2611.05296 (held version, sha256 31134e8d098ff93ca941097a6dd864cef12b6344e5d41c53281f43af7e683e8d), Theorem 6.6, p.32 (PDF p.34); proof pp.32–33 (PDF pp.34–35)

import Mathlib
import Definitions.Def_MaskingHardness_Supplement_IsHighestFidelityResponse
import Definitions.Def_MaskingHardness_Supplement_IsMonotoneFidelity
import Definitions.Def_MaskingHardness_Supplement_IsMonotoneMixingFidelity

namespace MaskingHardness.Supplement

/-- **Theorem 6.6** (Universal Masking Channels – Common Post-Processing) (Gopalan–Prabhakaran–Tankala, *Universal Hardness From Masking Channels*, arXiv:2611.05296, held version sha256 31134e8d…3e8d, Theorem 6.6,
printed p.32 = PDF p.34; proof printed pp.32–33 = PDF pp.34–35).

There exists a common highest-fidelity response function `Ŵ = Ŵ_h` for all monotone fidelity
functions. There exists a (different) common highest-fidelity response function `Ŵ = Ŵ_h` for
all monotone mixing fidelity functions.

**Formalization Note** For every `k`: `∃ Ŵ, ∀ h` monotone, `Ŵ` is an (exact, `γ = 0`)
highest-fidelity response for `h` (Definition 1.18: feasible and attaining the maximum at every
`z ∈ Δ_k`, including `z` with zero entries); and likewise for monotone mixing `h`. "(different)"
is a remark, not a claim that the two responses differ. The claim is made for every `h` of the
Definition 1.19 form with `h0 : ℝ → ℝ̄` nondecreasing, without the closed–proper–concave
requirement of a fidelity function. -/
theorem theorem_6_6 {k : ℕ} :
    (∃ What : (Fin k → ℝ) → Matrix (Fin k) (Fin k) ℝ,
      ∀ h : Fin k → (Fin k → ℝ) → EReal, IsMonotoneFidelity h →
        IsHighestFidelityResponse h 0 What) ∧
    (∃ What : (Fin k → ℝ) → Matrix (Fin k) (Fin k) ℝ,
      ∀ h : Fin k → (Fin k → ℝ) → EReal, IsMonotoneMixingFidelity h →
        IsHighestFidelityResponse h 0 What) := by sorry

end MaskingHardness.Supplement
