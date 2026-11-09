-- Prove2me | Theorems.Thm_LinfContractionFP_section_4_solve_loop
-- name    : LinfContractionFP.section_4_solve_loop
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:15:50.226194+00:00
-- url     : https://prove2.me/theorems/eb014c4b-2378-4f12-8018-ec8721444d4c
-- title:
--   Section 4 and Remark 1 — Solve's loop returns an $\varepsilon$-near fixed point
-- statement:
--   Let $d\ge2$, $0<\gamma\le1$, $\varepsilon>0$ and let $f$ be a $(1-\gamma)$-contraction of $[0,1]^d$. Suppose that every call $\mathrm{Label}(L,U;\tau,\varepsilon)$ with $\tau>0$ returns either an $\varepsilon$-near fixed point of $f$ or a $\tau$-accurate labeling of $[L,U]$ (Definition 1). Then Algorithm 1 returns an $\varepsilon$-near fixed point of $f$, and its main loop runs at most
--   $$\big\lceil\log_{8/7}(1/\varepsilon)\big\rceil$$
--   times, so Label is called at most that many times.
--
--   The proof is the invariant $x^*\in[L,U]$ for the cube of side $D$, maintained by Remark 1.
--
--   Differences from the source:
--   - generalization: Label (Algorithm 4) → any procedure lab returning, for every box and every τ > 0, an ε-near fixed point or a τ-accurate labeling; reason: this is Label's specification (Corollary 2); Algorithm 4 meets it, so the statement specializes to the paper's
--   - reading: within O(log(1/ε)) iterations; Solve calls Label a total log_{8/7}(1/ε) times → the loop runs at most ⌈log_{8/7}(1/ε)⌉ times; reason: the iteration count of 'while D > ε' with D ← 7D/8
-- source:
--   Soleymani–Farina, A Quasipolynomial Algorithm for ℓ∞ Contractions, arXiv:2610.30122 (held version, sha256 595b44934c28fc12e2cc9cb0fb7c0750d40a24fcd5661627726f3915a24cc0de), Section 4, pp.5–6; Algorithm 1, p.6; Remark 1, p.7; Section 6.5, p.20

import Mathlib
import Definitions.Def_LinfContractionFP_IsContraction
import Definitions.Def_LinfContractionFP_IsNearFixed
import Definitions.Def_LinfContractionFP_IsAccurateLabeling
import Definitions.Def_LinfContractionFP_solveLoop

namespace LinfContractionFP

/-- Section 4 with Remark 1: the loop of Algorithm 1 is correct. If every call `Label(L, U; τ, ε)`
returns either an `ε`-near fixed point or a `τ`-accurate labeling of `[L, U]` (Definition 1),
then Solve's loop (Algorithm 1, `d ≥ 2`) returns an `ε`-near fixed point of `f`, and its loop
runs at most `⌈log_{8/7}(1/ε)⌉` times, so Label is called at most that many times.

Soleymani–Farina, *A Quasipolynomial Algorithm for ℓ∞ Contractions*, arXiv:2610.30122 (held
version, sha256 595b4493…), Section 4, pp.5–6, Algorithm 1, p.6, and Remark 1, p.7: "Our algorithm maintains a search
cube [L, U] = ∏_{i=1}^d [L_i, U_i] of side U_i − L_i = D, that contains the true fixed point x*.
[...] Hence, within O(log(1/ε)) iterations, x* is contained within a box of size ε. The midpoint
q := (L + U)/2 is therefore a ε/2-near fixed point [...] Therefore, it is always safe to update
L_i ← L_i + D/8 when ℓ_{i,−} = hi and U_i ← U_i − D/8 when ℓ_{i,−} = lo." Remark 1: "any
D/8-accurate labeling implies (2)." Section 6.5, p.20: "Solve calls Label a total
log_{8/7}(1/ε) times."

**Formalization Note.** Label is the parameter `lab`, with the specification of Algorithm 4
(the paper's Corollary 2) for every box and every accuracy `τ > 0`. The loop of Algorithm 1 runs
`solveIterations ε` times (at most), and one call of `lab` is made per iteration. -/
theorem section_4_solve_loop {ι : Type} [Fintype ι] (hd : 2 ≤ Fintype.card ι) (γ : ℝ)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (f : (ι → ℝ) → (ι → ℝ)) (hf : IsContraction γ f) (ε : ℝ)
    (hε : 0 < ε) (lab : (ι → ℝ) → (ι → ℝ) → ℝ → ℝ → (ι → ℝ) ⊕ (ι × Bool → Lbl))
    (hlab : ∀ (L U : ι → ℝ) (τ : ℝ), 0 < τ →
      (∀ x, lab L U τ ε = Sum.inl x → IsNearFixed f ε x) ∧
      (∀ ℓ, lab L U τ ε = Sum.inr ℓ →
        ∀ xs ∈ unitCube ι, f xs = xs → IsAccurateLabeling τ L U xs ℓ)) :
    IsNearFixed f ε (solveLoop lab ε) ∧
      solveIterations ε ≤ Nat.ceil (Real.logb (8 / 7) (1 / ε)) := by sorry

end LinfContractionFP
