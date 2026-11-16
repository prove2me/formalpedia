-- Prove2me | Theorems.Thm_FourWayStream_ARHM_Supplement_regression_sampling_lower_bounds
-- name    : FourWayStream.ARHM.Supplement.regression_sampling_lower_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:02:10.626985+00:00
-- url     : https://prove2.me/theorems/5e54eb6e-af16-4473-b43d-107fba07fa3e
-- title:
--   Theorem 5.19 — regression sampling needs $\Omega(\sqrt N)$ classical bits in random order and $\Omega(m)$ qubits data-first
-- statement:
--   Let $N$ be even, $2\le m\le\lfloor\sqrt N\rfloor$, $L\ge1$, $F$ a one-factorization of $K_N$ with any orientation of its pairs, and consider the stream $\mathrm{RS}_{N,m}(B_F)$ with flat promised $y$ and the correctness notion of Definition 5.17 (the joint transcript is within total variation distance $1/3$ of $p_{B_{k_1},y}\otimes\cdots\otimes p_{B_{k_m},y}$ for every promised $y$ and request list). Then:
--   1. every classical algorithm that is correct in random order uses at least $\sqrt{N-1}/6-1$ bits;
--   2. every quantum algorithm that is correct in data-first order uses at least $m/2-1$ qubits.
--
--   Consequently
--   $$S^C_{\mathrm{rand}}(\mathrm{RS}_{N,m}(B_F))=\Omega(\sqrt N),\qquad S^Q_{\mathrm{data\text{-}first}}(\mathrm{RS}_{N,m}(B_F))=\Omega(m),$$
--   with positive constants independent of $N,m,L,F$ and the orientation.
--
--   The hardness cannot come from the matrices, which are orthogonal and have two nonzero entries per row; it comes from consumability. The quantum random-order upper bound (Remark 5.20) is not part of this theorem.
--
--   **Formalization Note** The paper writes $\Omega(\cdot)$; the proof transfers the explicit bounds $\sqrt{N-1}/6-1$ (Proposition 5.12) and $m/2-1$ (Proposition 5.13 with $s=m$), and the $\Omega$ forms are stated as $c\sqrt N\le$ space for $N\ge N_0$ and $cm\le$ space for $m\ge m_0$, with $c>0$, $N_0$, $m_0$ universal.
--
--   Differences from the source:
--   - reading: §4.2: a classical controller applies, for every item, a circuit from a fixed finite set of gates and measurement operators → every item is processed by an arbitrary quantum instrument (finite complete Kraus family) on the memory C^d; the finite gate set is not modelled; reason: §4.2 is ambiguous: it states that the lower bounds hold for arbitrary channels ("they only use that the memory between two items is a state of the given number of qubits and bits"); this is the base mission's reading
--   - generalization: §4.2: a step may depend on the stage only through stored memory; space is the maximum live memory including workspace inside a step → lower bounds hold for algorithms whose instruments (transitions) may also depend on the stage, charging only the memory between two items (⌈log₂ d⌉ qubits, ⌈log₂ S⌉ bits); reason: a larger algorithm class and a smaller charge; the paper's algorithms are the stage-independent ones, whose memory between items is at most their space
--   - generalization: L = (100m)² copies (Definition 5.17) → every number L ≥ 1 of copies; reason: the transferred lower bounds (Prop 5.12, Cor 5.15) hold for every L ≥ 1, as remarked after Theorem 5.3; L = (100m)² is a special case
--   - encoding: S^C_rand = Ω(√N), S^Q_data-first = Ω(m) → the explicit bounds √(N−1)/6 − 1 and m/2 − 1, plus c√N ≤ space for N ≥ N₀ and cm ≤ space for m ≥ m₀ with universal c > 0, N₀, m₀; reason: the constants established by the proofs of Prop 5.12 and Prop 5.13 that Appendix A transfers; both forms imply the Ω-bounds
--   - encoding: an observation (j, y_j, ℓ) with y_j a real number; an output index J = (e, b) → an item carrying a real number; outputs Option (Sym2 (Fin N) × Bool), with ideal probability 0 outside the rows of B_{k_t}; reason: same instances; an algorithm may also write outputs after observations, which are ignored
--   - encoding: [N], [m], [w], [r], [n], bits in {0,1}, edges {u, v} → Fin N, Fin m, Fin w, Fin r, Fin n (0-based), Bool, Sym2; reason: Lean convention; same instances
-- source:
--   Nadezhda Voronova, STOC 2027 submission #1371 (October 2026), p.27, Theorem 5.19 (proof p.43, Appendix A); explicit constants from Proposition 5.12 (p.24) and Corollary 5.15 (p.25)

import Mathlib
import Definitions.Def_FourWayStream_ARHM_Stream
import Definitions.Def_FourWayStream_ARHM_Supplement_Regression

set_option autoImplicit false
open Classical

namespace FourWayStream.ARHM.Supplement

open QAlgorithms
open scoped Matrix

/-- Theorem 5.19 (Lower bounds for regression sampling), p.27 (proof p.43). For every even `N`, every
`2 ≤ m ≤ ⌊√N⌋`, every number `L ≥ 1` of copies, every one-factorization `F` and every orientation,
the stream `RS_{N,m}(B_F)` with flat promised `y`, under the correctness notion of Definition 5.17
(joint transcript within total variation distance `1/3` of the ideal product law), satisfies:
every classical random-order algorithm uses at least `√(N − 1)/6 − 1` bits and every quantum
data-first algorithm at least `m/2 − 1` qubits; hence `S^C_rand = Ω(√N)` and
`S^Q_data-first = Ω(m)` with positive universal constants. -/
theorem regression_sampling_lower_bounds :
    (∀ (N m L : ℕ), Even N → 2 ≤ m → m ≤ Nat.sqrt N → 1 ≤ L →
      ∀ F : Fin (N - 1) → Finset (Sym2 (Fin N)), IsOneFactorization F →
      ∀ ori : Sym2 (Fin N) → Fin N × Fin N, IsOrientation ori →
      (∀ A : CIOAlg (RSItem N m L) (Option (Sym2 (Fin N) × Bool)), A.Valid →
          CRSCorrectRand A (fun k => rowSet (F k)) (hmB F ori) (flatPromise N) (1 / 3) →
          Real.sqrt ((N : ℝ) - 1) / 6 - 1 ≤ A.space) ∧
      (∀ A : QIOAlg (RSItem N m L) (Option (Sym2 (Fin N) × Bool)), A.Valid →
          QRSCorrectDataFirst A (fun k => rowSet (F k)) (hmB F ori) (flatPromise N) (1 / 3) →
          (m : ℝ) / 2 - 1 ≤ A.space)) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ (N m L : ℕ), N₀ ≤ N → Even N → 2 ≤ m → m ≤ Nat.sqrt N →
      1 ≤ L → ∀ F : Fin (N - 1) → Finset (Sym2 (Fin N)), IsOneFactorization F →
      ∀ ori : Sym2 (Fin N) → Fin N × Fin N, IsOrientation ori →
      ∀ A : CIOAlg (RSItem N m L) (Option (Sym2 (Fin N) × Bool)), A.Valid →
        CRSCorrectRand A (fun k => rowSet (F k)) (hmB F ori) (flatPromise N) (1 / 3) →
        c * Real.sqrt N ≤ A.space) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ (N m L : ℕ), m₀ ≤ m → Even N → 2 ≤ m → m ≤ Nat.sqrt N →
      1 ≤ L → ∀ F : Fin (N - 1) → Finset (Sym2 (Fin N)), IsOneFactorization F →
      ∀ ori : Sym2 (Fin N) → Fin N × Fin N, IsOrientation ori →
      ∀ A : QIOAlg (RSItem N m L) (Option (Sym2 (Fin N) × Bool)), A.Valid →
        QRSCorrectDataFirst A (fun k => rowSet (F k)) (hmB F ori) (flatPromise N) (1 / 3) →
        c * m ≤ A.space) := by sorry

end FourWayStream.ARHM.Supplement
