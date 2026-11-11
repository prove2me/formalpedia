-- Prove2me | Theorems.Thm_LiuHelsenDesigns_OneD_lemma_2
-- name    : LiuHelsenDesigns.OneD.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T11:08:24.125818+00:00
-- url     : https://prove2.me/theorems/22f2a7d2-d6a7-4a5f-bdc6-009e433a77dc
-- title:
--   Lemma 2 — gap amplification to relative-error designs
-- statement:
--   There is a positive absolute constant C. Let ν be an n-qubit probability law on unitaries, with $k\ge1$, $0<\Delta\le1$, and $g(\nu,k)\le1-\Delta$. For every $0<\varepsilon\le1$,
--
--   $$
--   L\ge\frac C\Delta(nk+\log_2(1/\varepsilon))\quad\Longrightarrow\quad\nu^{*L}\text{ is an }\varepsilon\text{-relative-error }k\text{-design}.
--   $$
--
--   This is a uniformly sufficient iteration threshold. Substituting a uniform positive gap gives the source’s second conclusion.
--
--   Differences from the source:
--   - reading: approximation errors and design order in the standing context → positive integer order and positive errors at most one (local exact blocks also allow zero); reason: the nontrivial precision regime of §2.1 and the surrounding construction
--   - encoding: uniform O(·) and Ω(1) statements → positive constants chosen before every size, order, precision and representation they are uniform over; reason: only Theorem 1 constants and its size threshold may depend on the fixed c
--   - reading: a sufficient iteration count written L=O(·) → all integer lengths above a uniform sufficient threshold, plus a bounded sufficient choice in Theorem 5; reason: an arbitrary small length satisfying an upper big-O bound is not a mixing guarantee
--   - encoding: unqualified logarithms inside O(·) resource or overlap bounds → binary logarithms inside bounds with uniform existential leading constants; reason: changing a fixed logarithm base multiplies these terms by a fixed positive factor, absorbed uniformly into the leading constants; explicit log₂ expressions are unchanged
-- source:
--   Guoding Liu, Jonas Helsen, STOC 2027 submission #221 (October 2026), p. 11, Lemma 2. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/221.pdf

import Definitions.Def_LiuHelsenDesigns_OneD_designs

namespace LiuHelsenDesigns.OneD
theorem lemma_2 : ∃ C : ℝ, 0 < C ∧
    ∀ n k : ℕ, 1 ≤ k → ∀ (ν : MeasureTheory.Measure (Mat n)),
      IsUnitaryLaw ν → ∀ Δ : ℝ, 0 < Δ → Δ ≤ 1 → essentialNorm ν k ≤ 1-Δ →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ L : ℕ,
        C / Δ * ((n : ℝ)*k + Real.logb 2 (1/ε)) ≤ L →
        RelativeDesign (powerLaw ν L) k ε := by sorry
end LiuHelsenDesigns.OneD
