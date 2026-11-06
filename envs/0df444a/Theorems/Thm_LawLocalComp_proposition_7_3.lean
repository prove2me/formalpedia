-- Prove2me | Theorems.Thm_LawLocalComp_proposition_7_3
-- name    : LawLocalComp.proposition_7_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:16:56.016389+00:00
-- url     : https://prove2.me/theorems/a9dbf7d8-eddf-4f30-b736-f62432b44c90
-- title:
--   Proposition 7.3 (Explicit structured map)
-- statement:
--   For rational $0<\varepsilon\le1$ put $\delta=\varepsilon/4$, $\rho=1+\delta$ and $r_N=\lceil\log_2(N/\delta)\rceil$. Use $r=r_N$ without a rank promise and otherwise $r=\min\{r_N,2\lceil\log_2(12q/\delta)\rceil\}$, $q\ge2$. Then the partition map of Lemma 7.2 with $(r,\delta,\rho)$:
--   1. satisfies (1) on every admitted selection of lattice-log-concave laws;
--   2. has at most $3+\lceil\log_\rho(3r/\delta)\rceil$ (32) rational atoms on lattice-log-concave inputs;
--   3. is a conditional-mean replacement preserving means and point masses;
--   4. runs in time polynomial in the input, $1/\varepsilon$, $\log N$ and, if supplied, $\log q$.
--
--   **Formalization Note** The machine reads $\varepsilon,N,q$ in binary and a unary pad of length $\lceil1/\varepsilon\rceil$ and is required to be correct on lattice-log-concave inputs.
--
--   Differences from the source:
--   - reading: otherwise r = min{r_N, 2⌈log₂(12q/δ)⌉} → under a rank promise alone r = 2⌈log₂(12q/δ)⌉; under both, the minimum; reason: r_N does not exist without a horizon
--   - reading: runs in time polynomial in the input, 1/ε, log N, and, if supplied, log q → PolyLawMap with ε, N, q in binary, a unary pad of length ⌈1/ε⌉₊, correct on lattice-log-concave inputs; reason: the literal reading; the claim concerns lattice-log-concave inputs
--   - reading: horizon N (no stated range) → N ≥ 1 for a horizon; reason: r_N = ⌈log₂(N/δ)⌉ needs N ≥ 1 to be a truncation level r ≥ 1
--   - encoding: running time claimed for rational 0 < ε ≤ 1 → the machine computes the map at 0 < ε ≤ 1 and returns its input law at every other rational ε; reason: PolyLawMap ranges over every parameter value, and the page claims nothing outside 0 < ε ≤ 1
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), Proposition 7.3, (32), p.13

import Mathlib
import Definitions.Def_LawLocalComp_structMap
import Definitions.Def_LawLocalComp_Contract
import Definitions.Def_LawLocalComp_IsGoodOutput
import Definitions.Def_LawLocalComp_IsLatticeLC
import Definitions.Def_LawLocalComp_PolyLawMap
import Definitions.Def_LawLocalComp_Resource_params

namespace LawLocalComp

/-- **Proposition 7.3 (Explicit structured map).**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), Proposition 7.3, (32), p.13.

For rational `0 < ε ≤ 1`, with `δ = ε/4`, `ρ = 1 + δ`, `r_N = ⌈log₂(N/δ)⌉`, and `r = r_N` without a rank
promise, otherwise `r = min{r_N, 2⌈log₂(12q/δ)⌉}` (`q ≥ 2`): the partition map `structMap ε R` of
Lemma 7.2 satisfies (1) on lattice-log-concave laws with at most `3 + ⌈log_ρ(3r/δ)⌉` atoms, is a
rational conditional-mean map preserving means and point masses, and runs in time polynomial in the
input, `1/ε`, `log N` and, if supplied, `log q`.

**Formalization Note.** The machine reads `ε`, `N`, `q` in binary and a unary pad of length `⌈1/ε⌉`,
and must be correct on lattice-log-concave inputs. The time claim is for `0 < ε ≤ 1`, as printed:
outside that range the machine returns its input law, so no running time is claimed for the values
`structMap` takes at `ε ≤ 0` or `ε > 1`. "Otherwise" covers both a rank-only and a
two-resource call; with rank only, only the rank term defines `r`. `N ≥ 1` is the range in which a
horizon is meaningful. -/
theorem proposition_7_3 :
    PolyLawMap (fun p : ℚ × Resource => p.1 :: p.2.params) (fun p => ⌈1 / p.1⌉₊) IsLatticeLC
        (fun p X => if 0 < p.1 ∧ p.1 ≤ 1 then structMap p.1 p.2 X else X) ∧
    ∀ ε : ℚ, 0 < ε → ε ≤ 1 → ∀ R : Resource,
      (∀ N : ℕ, R = .horizon N → 1 ≤ N) → (∀ q : ℕ, R = .rank q → 2 ≤ q) →
      (∀ N q : ℕ, R = .both N q → 1 ≤ N ∧ 2 ≤ q) →
      Contract (structMap ε R) R IsLatticeLC (1 + ε) ∧
      ∀ X : Law, IsLatticeLC X → IsGoodOutput X (structMap ε R X) ∧
        ((structMap ε R X).w.support.card : ℝ) ≤
          3 + ⌈Real.logb (1 + (ε : ℝ) / 4) (3 * structR ε R / ((ε : ℝ) / 4))⌉₊ := by sorry

end LawLocalComp
