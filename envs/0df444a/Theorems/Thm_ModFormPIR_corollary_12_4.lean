-- Prove2me | Theorems.Thm_ModFormPIR_corollary_12_4
-- name    : ModFormPIR.corollary_12_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:04:16.742205+00:00
-- url     : https://prove2.me/theorems/31689790-a437-4788-b061-b7cfc15720fa
-- title:
--   Corollary 12.4, p.66 — sparse expansions with exponents $\eta_{q,s}(\vartheta,\nu)$ and $\eta_{q,s}$, and their numerical bounds
-- statement:
--   Fix an odd prime $q$, an integer $s\in[2,q]$ and a feasible pair $(\vartheta,\nu)$, and let $d$ grow. Then there is a $(k,s)$-sparse quadratic-phase delta expansion over $\mathbb Q(\zeta_q)$ on $\mathbb Z_q^d$ with permutation-invariant support and
--   $$k\le q^{(\eta_{q,s}(\vartheta,\nu)+o(1))d};$$
--   the same holds with $\eta_{q,s}$ in place of $\eta_{q,s}(\vartheta,\nu)$. Moreover, $\eta_{3,2}\le0.820340$, $\eta_{3,3}\le0.732672$, $\eta_{5,4}\le0.702450$, $\eta_{5,5}\le0.653434$, $\eta_{7,6}\le0.652057$, $\eta_{7,7}\le0.619701$, $\eta_{11,10}\le0.607791$, $\eta_{11,11}\le0.590014$, and as $q$ grows
--   $$\eta_{q,q}\le\frac12+\frac{\frac12\ln(\pi e/6)+o(1)}{\ln q}\le\frac12+\frac{0.255+o(1)}{\log_2q}.$$
--
--   This packages Theorem 12.2 with the support-size bounds, and it is the input of Main Theorem 5.5.
--
--   Differences from the source:
--   - encoding: k ≤ q^{(η+o(1))d}, d growing → one g → 0 per (q, s, ϑ, ν), for all d ≥ 1 and every primitive root ζ; reason: the meaning of o(1)
--   - encoding: the chain η_{q,q} ≤ A ≤ B with o(1) terms → two bounds on η_{q,q}, each with its own h → 0; reason: the middle inequality is arithmetic: ½ log₂(πe/6) < 0.255
-- source:
--   Henzinger, Ragavan, Doubly-Efficient Private Information Retrieval from Modular Forms, STOC 2027 submission (manuscript sha256 2442f3db…), Corollary 12.4, p.66 (PDF p.70)

import Mathlib
import Definitions.Def_ModFormPIR_Expansion

open Filter Topology

set_option autoImplicit false

namespace ModFormPIR

/-- **Corollary 12.4**, p.66. Henzinger, Ragavan, *Doubly-Efficient Private Information Retrieval from Modular Forms*, STOC 2027 submission (manuscript sha256 2442f3db…).
For `q` an odd prime, `s ∈ [2, q]`, `(ϑ, ν)` feasible: a `(k, s)`-sparse quadratic-phase delta expansion over `ℚ(ζ_q)` on `ℤ_q^d` with permutation-invariant
support and `k ≤ q^{(η_{q,s}(ϑ,ν)+o(1))d}`, and likewise for `η_{q,s}`; the eight six-digit bounds; and `η_{q,q} ≤ 1/2 + (½ ln(πe/6) + o(1))/ln q ≤ 1/2 + (0.255 + o(1))/log₂ q`.

**Formalization Note.** One `g → 0` per `(q, s, ϑ, ν)`, for all `d ≥ 1` and every primitive root `ζ`. Each `o(1)` as `q → ∞` is one `h → 0`, the last inequality of the chain being
stated as a bound on `η_{q,q}`. -/
theorem corollary_12_4 :
    (∀ (q s : ℕ) [NeZero q], q.Prime → Odd q → 2 ≤ s → s ≤ q → ∀ ϑ ν : ℝ, Feasible q s ϑ ν →
      ∃ g : ℕ → ℝ, Tendsto g atTop (𝓝 0) ∧ ∀ (d : ℕ) (_ : 1 ≤ d) (ζ : CyclotomicField q ℚ)
        (_ : IsPrimitiveRoot ζ q),
        ∃ (𝒲 : Finset (Fin d → ZMod q)) (𝒜 : Finset (ZMod q))
          (c : (Fin d → ZMod q) → ZMod q → CyclotomicField q ℚ),
          IsDeltaExpansion ζ c ∧ HasSupport c (𝒲 : Set (Fin d → ZMod q)) (𝒜 : Set (ZMod q)) ∧
          IsPermInvariant (𝒲 : Set (Fin d → ZMod q)) ∧ 𝒜.card ≤ s ∧
          (𝒲.card : ℝ) ≤ (q : ℝ) ^ ((eta q s ϑ ν + g d) * d)) ∧
    (∀ (q s : ℕ) [NeZero q], q.Prime → Odd q → 2 ≤ s → s ≤ q →
      ∃ g : ℕ → ℝ, Tendsto g atTop (𝓝 0) ∧ ∀ (d : ℕ) (_ : 1 ≤ d) (ζ : CyclotomicField q ℚ)
        (_ : IsPrimitiveRoot ζ q),
        ∃ (𝒲 : Finset (Fin d → ZMod q)) (𝒜 : Finset (ZMod q))
          (c : (Fin d → ZMod q) → ZMod q → CyclotomicField q ℚ),
          IsDeltaExpansion ζ c ∧ HasSupport c (𝒲 : Set (Fin d → ZMod q)) (𝒜 : Set (ZMod q)) ∧
          IsPermInvariant (𝒲 : Set (Fin d → ZMod q)) ∧ 𝒜.card ≤ s ∧
          (𝒲.card : ℝ) ≤ (q : ℝ) ^ ((etaInf q s + g d) * d)) ∧
    etaInf 3 2 ≤ 0.820340 ∧ etaInf 3 3 ≤ 0.732672 ∧ etaInf 5 4 ≤ 0.702450 ∧
    etaInf 5 5 ≤ 0.653434 ∧ etaInf 7 6 ≤ 0.652057 ∧ etaInf 7 7 ≤ 0.619701 ∧
    etaInf 11 10 ≤ 0.607791 ∧ etaInf 11 11 ≤ 0.590014 ∧
    (∃ h : ℕ → ℝ, Tendsto h atTop (𝓝 0) ∧ ∀ (q : ℕ) [NeZero q], q.Prime → Odd q →
      etaInf q q ≤ 1 / 2 + (1 / 2 * Real.log (Real.pi * Real.exp 1 / 6) + h q) / Real.log q) ∧
    (∃ h : ℕ → ℝ, Tendsto h atTop (𝓝 0) ∧ ∀ (q : ℕ) [NeZero q], q.Prime → Odd q →
      etaInf q q ≤ 1 / 2 + (0.255 + h q) / Real.logb 2 q) := by sorry

end ModFormPIR
