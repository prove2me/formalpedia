-- Prove2me | Theorems.Thm_ModFormPIR_main_theorem_5_5
-- name    : ModFormPIR.main_theorem_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:59:28.990007+00:00
-- url     : https://prove2.me/theorems/3d8aa4a6-0e8f-44b3-9c8f-35af54b3d4ed
-- title:
--   Main Theorem 5.5, p.22 — $s$-server schemes with exponents $\eta_{q,s}(\vartheta,\nu)$ and $\eta_{q,s}$, for all odd primes $q\ge s\ge2$
-- statement:
--   Let $q$ be an odd prime and $s\in[2,q]$ an integer. For every feasible pair $(\vartheta,\nu)$ there is an $s$-server doubly-efficient PIR scheme with exponent $\eta_{q,s}(\vartheta,\nu)$, and there is one with exponent $\eta_{q,s}$. Numerically,
--   $$\eta_{3,2}<0.8204,\ \eta_{3,3}<0.7327,\ \eta_{5,4}<0.7025,\ \eta_{5,5}<0.6535,\ \eta_{7,6}<0.6521,\ \eta_{7,7}<0.6198,\ \eta_{11,10}<0.6078,\ \eta_{11,11}<0.5901,$$
--   and
--   $$\eta_{q,q}\le\frac12+\frac{0.255+o(1)}{\log_2q}\quad(q\to\infty).$$
--   Consequently, as $s\to\infty$ there are $s$-server schemes with exponent $\frac12+\frac{0.255+o(1)}{\log_2s}$.
--
--   Each server stores exactly $n+1$ bits and reads and returns $n^{\eta+o(1)}$ of them, so storage has one bit of overhead over the database while the server time is polynomially sublinear. This is the central result of the paper.
--
--   **Formalization Note** One finite program triple and one $g\to0$ per $(q,s)$. No real parameter is an input: since $\eta_{q,s}\le\eta_{q,s}(\vartheta,\nu)$ and the scheme's definition is monotone in the exponent, the feasible-pair clause needs no digits of $(\vartheta,\nu)$. For the limit clauses, $h$ is defined on all naturals, with no constraint from any finite set of arguments.
--
--   Differences from the source:
--   - reading: "word operations" (no machine named) → word RAM with the published core, plus probe and coin, for all W ≥ b(⌊log₂ n⌋ + 1); reason: the source names no machine
--   - reading: "reads and sends back" → the answer is the list of bits probed, in order; reason: one list, so a server cannot send what it did not read
--   - reading: public parameters "sampled in expected polylog(n) time" → Las Vegas sampler: measurable accept time, cost ∞ off accepting runs, and every accepting run gives good parameters; reason: the source’s algorithm constructs a prime; correctness holds for every output
--   - encoding: n^{ρ+o(1)}, polylog(n), O(log² n) → (n+1)^{ρ+g n} with one g → 0, C·L^K, C·L² with L = ⌊log₂(n+2)⌋+1; reason: the meaning of the asymptotics; n+1 avoids 1^x = 1 at n = 1 and changes no exponent
--   - encoding: server time summed over the s servers → a bound per server; reason: for fixed s the factor s is absorbed by g
--   - reading: "there is an s-server scheme with exponent η" (the proof picks a feasible pair for each ε) → one finite program per (q, s) serving all n, with one g → 0; reason: Definition 5.1 is one scheme on all database sizes; a uniform program can reach the infimum through rational pairs
--   - encoding: "on database of n ∈ ℕ bits"; ρ ∈ [0, 1] → n ≥ 1; ρ any real; reason: there is no index at n = 0; η ∈ [0,1], and exponents above 1 at small s in the last clause are met by the trivial scheme
--   - encoding: o(1) as q → ∞ and as s → ∞ → one h : ℕ → ℝ with h → 0, for all odd primes q and all s ≥ 2; reason: the meaning of o(1); the value at finitely many arguments is unconstrained
-- source:
--   Henzinger, Ragavan, Doubly-Efficient Private Information Retrieval from Modular Forms, STOC 2027 submission (manuscript sha256 2442f3db…), Main Theorem 5.5, p.22 (PDF p.26), with Definition 5.1, p.21, Definition 5.4, pp.21–22

import Mathlib
import Definitions.Def_ModFormPIR_Scheme
import Definitions.Def_ModFormPIR_Exponent

open Filter Topology

set_option autoImplicit false

namespace ModFormPIR

/-- **Main Theorem 5.5** (Track 3: Jacobi forms), p.22. Henzinger, Ragavan, *Doubly-Efficient Private Information Retrieval from Modular Forms*, STOC 2027 submission (manuscript sha256 2442f3db…).
For every odd prime `q` and `s ∈ [2, q]`: an `s`-server doubly-efficient PIR scheme with exponent `η_{q,s}(ϑ,ν)`
for each feasible pair, and with exponent `η_{q,s}`; the eight numeric bounds; and the two limits as `q, s → ∞`.

**Formalization Note.** `HasScheme` asks for one finite program triple and one `g → 0` per `(q, s)`, for all `n`: no
real parameter is an input, since `(ϑ, ν)` only bounds the exponent. The two limits are one `h → 0` each; for small `s`, `h s` is
free, and the exponent may exceed `1`, where the trivial scheme applies. -/
theorem main_theorem_5_5 :
    (∀ (q s : ℕ) [NeZero q], q.Prime → Odd q → 2 ≤ s → s ≤ q → ∀ ϑ ν : ℝ, Feasible q s ϑ ν →
      HasScheme s (eta q s ϑ ν)) ∧
    (∀ (q s : ℕ) [NeZero q], q.Prime → Odd q → 2 ≤ s → s ≤ q → HasScheme s (etaInf q s)) ∧
    etaInf 3 2 < 0.8204 ∧ etaInf 3 3 < 0.7327 ∧ etaInf 5 4 < 0.7025 ∧ etaInf 5 5 < 0.6535 ∧
    etaInf 7 6 < 0.6521 ∧ etaInf 7 7 < 0.6198 ∧ etaInf 11 10 < 0.6078 ∧ etaInf 11 11 < 0.5901 ∧
    (∃ h : ℕ → ℝ, Tendsto h atTop (𝓝 0) ∧ ∀ (q : ℕ) [NeZero q], q.Prime → Odd q →
      etaInf q q ≤ 1 / 2 + (0.255 + h q) / Real.logb 2 q) ∧
    (∃ h : ℕ → ℝ, Tendsto h atTop (𝓝 0) ∧ ∀ s : ℕ, 2 ≤ s →
      HasScheme s (1 / 2 + (0.255 + h s) / Real.logb 2 s)) := by sorry

end ModFormPIR
