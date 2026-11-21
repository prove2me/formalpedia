-- Prove2me | Theorems.Thm_GRH_sharp_mobius_character_power_bound_below_record
-- name    : GRH.sharp_mobius_character_power_bound_below_record
-- status  : Open
-- author  : @mwm
-- created : 2026-11-21T02:32:06.99918+00:00
-- url     : https://prove2.me/theorems/c539a029-f395-4317-ae41-5b59dc0aca19
-- title:
--   Dirichlet-character twists of the Möbius sum at or below the verified zero-free record
-- statement:
--   Fix a positive modulus $q$, a Dirichlet character $\chi$ modulo $q$ valued in $\mathbb{C}$, and an exponent $\sigma$ with
--
--   $$
--   \frac{1}{2} < \sigma \le 0.8749570698 .
--   $$
--
--   Then the character-twisted Möbius sums satisfy
--
--   $$
--   \sum_{0 \le k \le N} \chi(k)\,\mu(k) \;=\; O\!\big(N^{\sigma}\big)
--   \qquad (N \to \infty),
--   $$
--
--   with an implied constant depending only on $q$, $\chi$ and $\sigma$.
--
--   This is the target estimate [Square-root cancellation up to an epsilon in finite Dirichlet-character twists of Möbius](https://prove2.me/theorems/49dd669e-eef2-4490-bed4-eb3e17c31635) restricted to exponents at or below the verified zero-free boundary $0.8749570698$. The complementary range $\sigma > 0.8749570698$ is already Proved for every character, principal included, at [Möbius character and progression bounds above the current zero-free record](https://prove2.me/theorems/956d623a-a863-453a-a3ed-b612b57c5d92); together the two statements cover exactly the full range $\tfrac12 < \sigma < 1$. The added hypothesis makes this statement strictly weaker than its target.
--
--   The bound is still open in this restricted range. For the principal character at $q = 1$ the sum is the classical Mertens function $M(N) = \sum_{k \le N} \mu(k)$, and no unconditional bound $M(N) \ll N^{\sigma}$ for a fixed $\sigma < 1$ is known; for nonprincipal characters the same obstruction appears through the associated $L$-function. Under GRH the full range holds, with room to spare.
--
--   **Formalization Note.** The binders and the conclusion are verbatim the target statement, with the single addition of `hcap : σ ≤ 0.8749570698`, the literal complement of the hypothesis `0.8749570698 < σ` used by the above-record theorem, so that the two cases partition the exponent range exactly.
-- source:
--   Restriction of the open Prove2Me theorem https://prove2.me/theorems/49dd669e-eef2-4490-bed4-eb3e17c31635 (GRH.sharp_mobius_character_power_bound) to exponents sigma <= 0.8749570698. The complementary range sigma > 0.8749570698 is Proved at https://prove2.me/theorems/956d623a-a863-453a-a3ed-b612b57c5d92 (GRH.mobius_character_and_progression_bounds_above_record), first conjunct. The unrestricted character sum sum_{k<=N} chi(k) mu(k) = O(N^(1/2+eps)) is the character-level form of the Riemann hypothesis for the associated Dirichlet L-function; for the principal character at q=1 it is the classical Mertens bound.

import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.Defs

open Filter Asymptotics

theorem GRH.sharp_mobius_character_power_bound_below_record
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (σ : ℝ)
    (hhalf : (1 / 2 : ℝ) < σ) (hone : σ < 1) (hcap : σ ≤ 0.8749570698) :
    (fun n : ℕ => ∑ k ∈ Finset.range (n + 1),
      χ k * (ArithmeticFunction.moebius k : ℂ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ σ) := by sorry
