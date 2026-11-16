-- Prove2me | Theorems.Thm_FourWayStream_ARHM_Supplement_constant_k_adversarial
-- name    : FourWayStream.ARHM.Supplement.constant_k_adversarial
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:12:31.249817+00:00
-- url     : https://prove2.me/theorems/13a86587-4197-4ab8-8ac7-e7391d983170
-- title:
--   Theorem 7.13 — constant $k$ in adversarial order: $\Omega_k(n^{1-1/d})$ classical bits, $\Omega_k(n^{1-2/d})$ quantum space, $d=\lfloor k/2\rfloor$
-- statement:
--   Fix $k\ge4$, let $d=\lfloor k/2\rfloor$, and let $n$ range over the multiples of $4k$. In adversarial order (error at most $1/3$ on every promise graph and every order of its edges, each edge arriving once):
--   1. classical streaming algorithms for $\mathrm{NGC}_{n,k}$ need $\Omega_k(n^{1-1/d})$ bits when $8k\mid n$;
--   2. if $d\ge3$, quantum streaming algorithms for $\mathrm{NGC}_{n,k}$ need $\Omega_k(n^{1-2/d})$ space.
--
--   For fixed $k\ge6$ this is a single-arrival separation between random order (Proposition 7.12: $k^{O(k)}\,\mathrm{polylog}\,n$ classical bits) and adversarial order, and the lower bound holds for quantum algorithms. Odd $k$ is included.
--
--   **Formalization Note** For each fixed $k$ there are $c>0$ and $n_0$, depending only on $k$, such that the space is at least $c\,n^{1-1/d}$ (classical, $n\ge n_0$, $8k\mid n$) and at least $c\,n^{1-2/d}$ (quantum, $d\ge3$, $n\ge n_0$, $4k\mid n$).
--
--   Differences from the source:
--   - reading: §4.2: a classical controller applies, for every item, a circuit from a fixed finite set of gates and measurement operators → every item is processed by an arbitrary quantum instrument (finite complete Kraus family) on the memory C^d; the finite gate set is not modelled; reason: §4.2 is ambiguous: it states that the lower bounds hold for arbitrary channels ("they only use that the memory between two items is a state of the given number of qubits and bits"); this is the base mission's reading
--   - generalization: §4.2: a step may depend on the stage only through stored memory; space is the maximum live memory including workspace inside a step → lower bounds hold for algorithms whose instruments (transitions) may also depend on the stage, charging only the memory between two items (⌈log₂ d⌉ qubits, ⌈log₂ S⌉ bits); reason: a larger algorithm class and a smaller charge; the paper's algorithms are the stage-independent ones, whose memory between items is at most their space
--   - encoding: Ω_k(n^{1−1/d}) bits, Ω_k(n^{1−2/d}) space → for each k: ∃ c > 0 and n₀ depending only on k with c·n^{1−1/d} ≤ ⌈log₂|σ|⌉, resp. c·n^{1−2/d} ≤ ⌈log₂ d⌉, for n ≥ n₀; reason: the standard meaning of Ω/O with the constant and threshold quantified before every varying parameter, as §4 uses them
--   - encoding: [N], [m], [w], [r], [n], bits in {0,1}, edges {u, v} → Fin N, Fin m, Fin w, Fin r, Fin n (0-based), Bool, Sym2; reason: Lean convention; same instances
-- source:
--   Nadezhda Voronova, STOC 2027 submission #1371 (October 2026), p.38, Theorem 7.13 (proof Appendix F, pp.50–51)

import Mathlib
import Definitions.Def_FourWayStream_ARHM_Supplement_NGC

set_option autoImplicit false
open Classical

namespace FourWayStream.ARHM.Supplement

open QAlgorithms
open scoped Matrix

/-- Theorem 7.13 (Constant `k` in adversarial order), p.38 (proof p.51). Fix `k ≥ 4` and let
`d = ⌊k/2⌋`. In adversarial order (error at most `1/3` for every promise graph and every order of its
edges): classical algorithms for `NGC_{n,k}` need `Ω_k(n^{1 − 1/d})` bits when `8k ∣ n`, and, if
`d ≥ 3`, quantum algorithms need `Ω_k(n^{1 − 2/d})` space when `4k ∣ n`; the constants and size
thresholds depend only on `k`. -/
theorem constant_k_adversarial (k : ℕ) (hk : 4 ≤ k) :
    (∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 8 * k ∣ n →
      ∀ {σ : Type} [Fintype σ] (A : CEdgeAlg (Fin n) σ), A.Valid → A.AdvErrorLE k (1 / 3) →
        c * (n : ℝ) ^ (1 - 1 / ((k / 2 : ℕ) : ℝ)) ≤ A.space) ∧
    (3 ≤ k / 2 → ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 4 * k ∣ n →
      ∀ A : QEdgeAlg (Fin n), A.Valid → A.AdvErrorLE k (1 / 3) →
        c * (n : ℝ) ^ (1 - 2 / ((k / 2 : ℕ) : ℝ)) ≤ A.space) := by sorry

end FourWayStream.ARHM.Supplement
