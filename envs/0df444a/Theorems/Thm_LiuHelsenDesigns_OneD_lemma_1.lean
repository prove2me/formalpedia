-- Prove2me | Theorems.Thm_LiuHelsenDesigns_OneD_lemma_1
-- name    : LiuHelsenDesigns.OneD.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T11:12:32.971454+00:00
-- url     : https://prove2.me/theorems/00aa8647-4088-4db2-ab0a-ae3a840b84c2
-- title:
--   Lemma 1 — gluing two block-brickwork layers
-- statement:
--   Let $n=m\xi$ with $m\ge2$ and $\xi\ge1$, and let $k\ge1$, $0<\varepsilon\le1$. Independent blocks on each adjacent patch pair are relative-error $\varepsilon/n$ designs on $2\xi$ qubits, each with nearest-neighbor depth at most d. If $\xi\ge\log_2(nk^2/\varepsilon)$, then their two alternating open-chain layers obey
--
--   $$
--   E\text{ is an }\varepsilon\text{-relative-error }k\text{-design},\qquad D(E)\le2d.
--   $$
--
--   This transports local design guarantees to the full chain while preserving the factor-two depth accounting.
--
--   Differences from the source:
--   - reading: approximation errors and design order in the standing context → positive integer order and positive errors at most one (local exact blocks also allow zero); reason: the nontrivial precision regime of §2.1 and the surrounding construction
--   - encoding: the two-layer architecture on adjacent patches → n=mξ, m≥2, independent laws on its m−1 adjacent pairs and general nearest-neighbor local implementations; reason: the source switches to the whole-chain construction when two patches do not fit; it is not a divisibility hypothesis on Theorem 1
-- source:
--   Guoding Liu, Jonas Helsen, STOC 2027 submission #221 (October 2026), p. 5, Lemma 1. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/221.pdf

import Definitions.Def_LiuHelsenDesigns_OneD_blocks
import Definitions.Def_LiuHelsenDesigns_OneD_routing

namespace LiuHelsenDesigns.OneD
open MeasureTheory
theorem lemma_1 (n ξ m k d : ℕ) (hξ : 1 ≤ ξ) (hm : 2 ≤ m) (hn : n = m*ξ)
    (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hpatch : Real.logb 2 ((n : ℝ)*k^2/ε) ≤ ξ)
    (ν : Fin (m-1) → Measure (Mat (2*ξ)))
    (hdesign : ∀ j, RelativeDesign (ν j) k (ε/n))
    (hdepth : ∀ j, ∀ᵐ U ∂ν j, ∃ C : List (List (PlacedUnitary (2*ξ))),
      NearestCircuit C ∧ placedCircuitMatrix C = U ∧ C.length ≤ d) :
    RelativeDesign (brickworkLaw n ξ m ν) k ε ∧
      ∀ᵐ U ∂brickworkLaw n ξ m ν, ∃ C : List (List (PlacedUnitary n)),
        NearestCircuit C ∧ placedCircuitMatrix C = U ∧ C.length ≤ 2*d := by sorry
end LiuHelsenDesigns.OneD
