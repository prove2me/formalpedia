-- Prove2me | Theorems.Thm_MonoApport_Flow_proposition_8
-- name    : MonoApport.Flow.proposition_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:39:39.1607+00:00
-- url     : https://prove2.me/theorems/21666c4a-4375-4683-b456-5287a39faf51
-- title:
--   Proposition 8, p. 19 — a solution is house-monotone iff f(p, H) ≤ f(p, H + 1) for every p and H
-- statement:
--   Let $f$ be a solution: it assigns to every instance $(p,H)$, with $p\in\mathbb N^n$ a vector of positive populations and $H$ a positive house size, one apportionment $f(p,H)\in\mathbb N_0^n$ with $\sum_i f_i(p,H)=H$. House monotonicity (axiom (c)) asks $f(p,H_1)\le f(p,H_2)\le f(p,H_3)$ componentwise whenever $H_1<H_2<H_3$.
--
--   **Proposition 8.** A solution $f$ is house-monotone if and only if for every $p\in\mathbb N^n$ and $H\in\mathbb N$,
--   $$f(p,H)\le f(p,H+1).$$
--
--   The proposition reduces the three-size axiom to a one-step condition, which is the form used to build the network-flow description of house-monotone apportionments.
--
--   Differences from the source:
--   - encoding: a solution is an apportionment method f with |f(p, H)| = 1, mapping each instance (p, H) ∈ ℕⁿ × ℕ to a vector of ℕ₀ⁿ with Σᵢ xᵢ = H → f : Solution, one function ∀ n, (Fin n → ℕ) → ℕ → (Fin n → ℕ) defined on vectors of every length, with IsSolution f asserting Σᵢ f(p, H)ᵢ = H on every instance; reason: single-valuedness is carried by the type; values of f off the instances (n = 0, a zero population, H = 0) are never used
--   - encoding: house monotonicity (c): for H₁ < H₂ < H₃ and every y ∈ f(p, H₂) there exist x ∈ f(p, H₁), z ∈ f(p, H₃) with x ≤ y ≤ z → HouseMonotone f: for all house sizes 0 < H₁ < H₂ < H₃, f(p, H₁) ≤ f(p, H₂) and f(p, H₂) ≤ f(p, H₃) componentwise; reason: for a solution every outcome is a singleton, so the existential quantifiers collapse to the unique values
-- source:
--   Cembrano, Correa, Schmidt-Kraepelin, Tsigonias-Dimitriadis & Verdugo, New Combinatorial Insights for Monotone Apportionment, arXiv:2410.23869v1, Proposition 8, p. 19 (proof §C.1, p. 38)

import Mathlib
import Definitions.Def_MonoApport_Flow_Setting

namespace MonoApport.Flow

/-- Proposition 8 (p. 19): a solution `f` is house-monotone if and only if
`f(p, H) ≤ f(p, H + 1)` for every `p ∈ ℕⁿ` and `H ∈ ℕ`. -/
theorem proposition_8 (f : Solution) (hf : IsSolution f) :
    HouseMonotone f ↔
      ∀ (n : ℕ) (p : Fin n → ℕ), IsPop p → ∀ H : ℕ, 0 < H → f p H ≤ f p (H + 1) := by sorry

end MonoApport.Flow
