-- Prove2me | Theorems.Thm_LaconicBarrier_Supplement_theorem_A_5
-- name    : LaconicBarrier.Supplement.theorem_A_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:39:01.601206+00:00
-- url     : https://prove2.me/theorems/8092468c-71fe-48b8-9124-c865f4d79059
-- title:
--   Theorem A.5 — an oracle test with short proofs gives $\mathrm{size}_L(n)\le 2^{O(\ell_P)}\mathrm{poly}(T,1/\Delta)$
-- statement:
--   Fix $\lambda$, $n$ and a proof system $\Pi = (G, P, V)$ for a relation $\mathcal R_L$, with proofs of at most $\ell_P$ bits. Let $V'$ be an oracle test for $\Pi$ at length $n$ (Definition A.3) with errors $\epsilon_c, \epsilon_s$ satisfying
--   $$
--   \Delta = 1 - \epsilon_c - \epsilon_s > 0 .
--   $$
--   Suppose that, given its random coins, $V'$ runs in time $T$ and makes at most $k \le T$ queries, and that $T$ also bounds the running time of $P$ and the witness lengths. As throughout §A.3, $T$ also bounds the statement length $n$. Then
--   $$
--   \mathrm{size}_L(n) \le 2^{O(\ell_P)}\,\mathrm{poly}(T, 1/\Delta),
--   $$
--   where the constants in $O(\cdot)$ and $\mathrm{poly}$ are universal.
--
--   This is the step of the multi-query barrier for adaptive SNARGs (Theorem 6.10) that uses no cryptography: a statistically sound oracle test with short proofs forces $L$ to have small circuits.
--
--   **Formalization Note** $2^{O(\ell_P)}\mathrm{poly}(T, 1/\Delta)$ is $2^{a\ell_P}(T + \lceil 1/\Delta\rceil + 2)^c$ with $a, c$ chosen before the relation, the proof system, $n$, the test and every bound. Running times are measured on the mission's machine model: one machine computes each next action of $V'$ from its coins and the replies so far within $T$ steps, and one machine computes $P$ within $T$ steps using at most $T$ coins.
--
--   Differences from the source:
--   - generalization: a proof system for an NP relation R_L → any relation Rel, with witnesses of statements of length n of length ≤ T; reason: the statement and proof never use polynomial-time decidability of the relation; every NP relation is a relation
--   - reading: given its random coins, V′ runs in time T and makes at most k ≤ T queries → one machine computes each next action of V′ from (coins, replies so far) within T steps on views of at most k replies; V′ never queries after k replies; k ≤ T; reason: the mission's machine model; the conclusion is poly(T), so the per-action reading does not change the class of bounds
--   - reading: T also bounds the running time of P and the witness lengths → witnesses of statements of length n have length ≤ T; P on (crs, x, w) with valid w uses at most T coins and is computed by one machine within T steps; honest proofs have length ≤ ℓ_P; reason: the page's hypothesis on the mission's machine model; ℓ_P is the proof length of Π (§A.3)
--   - reading: (§A.3, p.73) 'Without loss of generality, the time bound T(λ, n) of the reduction also bounds all lengths and running times below' → n ≤ T; reason: the section's standing convention (the statement length is one of those lengths)
--   - encoding: proofs together with a failure symbol are encoded in ℓ_P + 1 bits → false-statement oracles return proofs of length ≤ ℓ_P + 1; reason: the reply format of §A.3
--   - encoding: size_L(n) ≤ 2^{O(ℓ_P)} poly(T, 1/∆) → ∃ a c chosen before all data: some circuit with ≤ 2^{a·ℓ_P}·(T + ⌈1/∆⌉ + 2)^c gates decides L on {0,1}^n; reason: universal constants; ⌈1/∆⌉ and 1/∆ differ by less than 1
--   - encoding: an oracle algorithm V′ run against stateless oracles → OracleTest (coins, next action) run for k + 1 actions; running out of actions rejects; reason: with at most k queries, k + 1 actions run the test to completion
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), Theorem A.5 and Definition A.3, pp.73–74 (PDF 76–77)

import Mathlib
import Definitions.Def_LaconicBarrier_Supplement_OracleTest
import Definitions.Def_LaconicBarrier_Supplement_SizeAtMost
import Definitions.Def_LaconicBarrier_RunsWithin

namespace LaconicBarrier.Supplement

/-- **Theorem A.5** (Jain, Mathialagan, Roy, *From Succinct Arguments to Proofs: Lower Bounds for
Obfuscation and SNARGs*, STOC 2027 submission (manuscript sha256 1af78662…), Theorem A.5, p.74):
an oracle test with short proofs gives small circuits. Let `V′` be an oracle test for `Π` at length
`n` with errors `ϵ_c, ϵ_s` satisfying `∆ = 1 − ϵ_c − ϵ_s > 0`. Suppose that, given its random coins,
`V′` runs in time `T` and makes at most `k ≤ T` queries, and that `T` also bounds the running time of
`P` and the witness lengths. Then `size_L(n) ≤ 2^{O(ℓ_P)} poly(T, 1/∆)`.

**Formalization Note** The constants are universal: `∃ a c` before the relation, the proof system,
`n`, the test and all bounds; `2^{O(ℓ_P)} poly(T, 1/∆)` is `2^{a·ℓ_P}(T + ⌈1/∆⌉ + 2)^c`. `ℓ_P` bounds
the honest proofs at length `n` (§A.3, p.73: "Proofs together with a failure symbol are encoded in
`ℓ_P + 1` bits"). "Runs in time `T` given its coins" is: one machine of the mission's model computes
each next action of `V′` from `(coins, replies so far)` within `T` steps; `P`'s running time is
bounded likewise on every proving key, with at most `T` coins. The section's
standing convention "the time bound `T(λ, n)` of the reduction also bounds all lengths and running
times below" (p.73) supplies `n ≤ T`. -/
theorem theorem_A_5 : ∃ a c : ℕ, ∀ (Rel : List Bool → List Bool → Prop) (S : SNARG)
    (n ℓP T k : ℕ) (V : OracleTest) (εc εs : ℝ),
    0 < 1 - εc - εs → n ≤ T → k ≤ T →
    (∀ x w : List Bool, x.length = n → Rel x w → w.length ≤ T) →
    (∀ (crs x w : List Bool) (ρ : Fin (S.pcoins crs x w) → Bool), x.length = n → Rel x w →
      (S.P crs x w ρ).length ≤ ℓP) →
    (∀ crs x w : List Bool, x.length = n → Rel x w → S.pcoins crs x w ≤ T) →
    (∃ M : KarpLiptonOM.OracleTM, ∀ (crs x w : List Bool) (ρ : Fin (S.pcoins crs x w) → Bool),
      x.length = n → Rel x w → RunsWithin M [crs, x, w, bits ρ] (S.P crs x w ρ) T) →
    (∀ (ρ : Fin V.coins → Bool) (h : List (List Bool × List Bool)) (crs : List Bool),
      k ≤ h.length → V.next ρ h ≠ .query crs) →
    (∃ M : KarpLiptonOM.OracleTM, ∀ (ρ : Fin V.coins → Bool) (h : List (List Bool × List Bool)),
      h.length ≤ k → RunsWithin M [bits ρ, otViewCode h] (V.next ρ h).code T) →
    V.IsTest S Rel n ℓP (k + 1) εc εs →
    SizeAtMost (Lang Rel) n (2 ^ (a * ℓP) * (T + ⌈1 / (1 - εc - εs)⌉₊ + 2) ^ c) := by sorry

end LaconicBarrier.Supplement
