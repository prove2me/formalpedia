-- Prove2me | Theorems.Thm_GreedNorm_tbounded_cost_le
-- name    : GreedNorm.tbounded_cost_le
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:47:18.811464+00:00
-- url     : https://prove2.me/theorems/3d782577-e110-441d-8184-32e4a5737706
-- title:
--   Definitions 2.1–2.2, used in the proof of Lemma 3.5 — a $t$-bounded vector satisfies $g(v)\le g(\bar t)$
-- statement:
--   Let $\epsilon>0$, $t$ a threshold vector and $\bar t$ its expansion. If $v\in\mathbb R^m_{\ge0}$ is $t$-bounded and $g$ is a monotone symmetric norm on $\mathbb R^m$, then
--
--   $$
--   g(v)\le g(\bar t).
--   $$
--
--   This is the step in the proof of Lemma 3.5 that bounds the cost of a $t$-bounded assignment by the cost of the threshold vector; it is the only use of the expansion.
--
--   Differences from the source:
--   - reading: implicit step 'σ is t-bounded, so g(load(σ)) ≤ g(t̄)' in the proof of Lemma 3.5 → explicit inequality g(v) ≤ g(expansion t) for every nonnegative t-bounded v; reason: the paper uses the step without stating it; this is its general form
--   - encoding: monotone symmetric norms on the orthant R^k_{≥0} → R_{≥0} → functions (Fin k → ℝ) → ℝ satisfying the public SymNormLoad.IsMonotoneSymmetricNorm (a norm on all of ℝ^k, monotone on the orthant); reason: every monotone symmetric norm on the orthant extends to ℝ^k by x ↦ g(|x|), and only orthant values are ever used; same instances
--   - encoding: t ∈ R^{|POS|}_{≥0}, t̄ ∈ R^m indexed by [m] → t : ℕ → ℝ (values on POS), expansion on Fin m with coordinate i the paper's i + 1; reason: Lean convention; same instances
-- source:
--   Gan–Huang–Umboh, Greed is All You Need: An Approximation Algorithm Framework for Nested Norm Covering and Packing Problems, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), Definitions 2.1–2.2, p.5 (PDF 7); used in the proof of Lemma 3.5, pp.6–7 (PDF 8–9)

import Mathlib
import Definitions.Def_SymNormLoad_IsMonotoneSymmetricNorm
import Definitions.Def_GreedNorm_IsThreshold
import Definitions.Def_GreedNorm_expansion
import Definitions.Def_GreedNorm_IsTBoundedVec

namespace GreedNorm

/-- **A `t`-bounded vector costs at most the expansion: `g(v) ≤ g(t̄)`.**
Gan–Huang–Umboh, *Greed is All You Need: An Approximation Algorithm Framework for Nested Norm
Covering and Packing Problems*, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), Definitions 2.1–2.2, p.5 (PDF 7): "The expansion of t is the vector t̄ ∈ R^m_{≥0} where
t̄i := tprev(i) for each i ∈ [m]. [...] A vector v is t-bounded if for every ℓ ∈ POS, the number of
entries in v that are larger than tℓ is at most ℓ−1"; used in the proof of Lemma 3.5, pp.6–7
(PDF 8–9): "[an assignment σ that] has cost g(load(σ)) ≤ B".

For `ε > 0`, a threshold vector `t`, a nonnegative `t`-bounded `v ∈ ℝ^m` and a monotone
symmetric norm `g` on `ℝ^m`,
$$ g(v) \le g(\bar t). $$

**Formalization Note** The expansion is `expansion m ε t` on `Fin m` (coordinate `i` is the
paper's `i + 1`). -/
theorem tbounded_cost_le {m : ℕ} (ε : ℝ) (hε : 0 < ε) (t : ℕ → ℝ) (ht : IsThreshold m ε t)
    (v : Fin m → ℝ) (hv : ∀ i, 0 ≤ v i) (hvt : IsTBoundedVec ε t v)
    (g : (Fin m → ℝ) → ℝ) (hg : SymNormLoad.IsMonotoneSymmetricNorm g) :
    g v ≤ g (expansion m ε t) := by sorry

end GreedNorm
