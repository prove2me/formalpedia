-- Prove2me | Theorems.Thm_MonoApport_Flow_theorem_3
-- name    : MonoApport.Flow.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:40:00.957754+00:00
-- url     : https://prove2.me/theorems/a55797fe-7a79-4997-9661-d84da64dd2ab
-- title:
--   Theorem 3, p. 21 — the apportionments of house-monotone, quota-compliant solutions are the seat counts A(x, H) of the extreme points of (1)-(4) with Φ(p, H) seats
-- statement:
--   Let $(p,H)$ be an instance: $p\in\mathbb N^n$ a vector of $n\ge1$ positive populations with total $P$, and $H\ge1$ a house size. Let $\mathcal A(p,H)$ be the set of vectors $f(p,H)$ over all house-monotone and quota-compliant solutions $f$ (§5, p. 19); let $\mathcal E(p,L)$ be the set of extreme points of the linear program (1)–(4) with $L$ seats, $A_i(x,H)=\sum_{\ell=1}^H x(i,\ell)$ the number of seats state $i$ receives among the first $H$, and $\Phi(p,H)$ the lookahead defined recursively on p. 20 through $S_k$, $k^\star$ and $\tau$.
--
--   **Theorem 3.** For every instance $(p,H)$,
--   $$\mathcal A(p,H)=\big\{A(x,H): x\in\mathcal E(p,\Phi(p,H))\big\}.$$
--
--   The theorem gives a polyhedral description of all apportionments that house-monotone and quota-compliant solutions can produce at house size $H$: they are the projections onto the first $H$ seats of the vertices of a network-flow polytope with $\Phi(p,H)$ seats.
--
--   **Formalization Note.** The equality is stated between subsets of $\mathbb R^n$: the image of $\mathcal A(p,H)\subseteq\mathbb N_0^n$ under the coordinatewise cast equals the image of $\mathcal E(p,\Phi(p,H))$ under $x\mapsto A(x,H)$. Solutions are families over every number of states, as in the paper.
--
--   Differences from the source:
--   - encoding: a solution is an apportionment method f with |f(p, H)| = 1, mapping each instance (p, H) ∈ ℕⁿ × ℕ to a vector of ℕ₀ⁿ with Σᵢ xᵢ = H → f : Solution, one function ∀ n, (Fin n → ℕ) → ℕ → (Fin n → ℕ) defined on vectors of every length, with IsSolution f asserting Σᵢ f(p, H)ᵢ = H on every instance; reason: single-valuedness is carried by the type; values of f off the instances (n = 0, a zero population, H = 0) are never used
--   - encoding: house monotonicity (c): for H₁ < H₂ < H₃ and every y ∈ f(p, H₂) there exist x ∈ f(p, H₁), z ∈ f(p, H₃) with x ≤ y ≤ z → HouseMonotone f: for all house sizes 0 < H₁ < H₂ < H₃, f(p, H₁) ≤ f(p, H₂) and f(p, H₂) ≤ f(p, H₃) componentwise; reason: for a solution every outcome is a singleton, so the existential quantifiers collapse to the unique values
--   - encoding: variables x(i, t) for seats t ∈ [L] = {1, …, L}, with prefix sums over ℓ = 1, …, t bounded by ⌊t pᵢ/P⌋ and ⌈t pᵢ/P⌉ → x : Fin n → Fin L → ℝ, column t : Fin L standing for seat t + 1; the bounds at column t are ⌊(t + 1) pᵢ/P⌋ and ⌈(t + 1) pᵢ/P⌉ on the sum over columns ℓ ≤ t; reason: 0-indexed relabelling of the seats; no instance changes
--   - encoding: k⋆ is a minimum over integers k ≥ 1, Φ(p, 1) a minimum and Φ(p, H + 1) a maximum → kStar and Phi p 1 use sInf on ℕ, Phi p (H + 2) uses sSup on ℕ; reason: the sets are nonempty (and the maximized set finite) at every argument where the paper uses them, so sInf and sSup are the paper's min and max; the junk value 0 of an empty set is never reached
--   - encoding: 𝒜(p, H) ⊆ ℕ₀ⁿ is compared with {A(x, H) : x ∈ ℰ(p, Φ(p, H))} ⊆ ℝⁿ → the image of 𝒜(p, H) under the coordinatewise cast ℕ → ℝ equals the image of ℰ(p, Φ(p, H)) under x ↦ A(x, H); reason: the cast is injective, so this is the paper's equality; comparing in ℝⁿ keeps every (a priori non-integral) A(x, H) in the right-hand side
-- source:
--   Cembrano, Correa, Schmidt-Kraepelin, Tsigonias-Dimitriadis & Verdugo, New Combinatorial Insights for Monotone Apportionment, arXiv:2410.23869v1, Theorem 3, p. 21 (proof §C.4, pp. 42–43)

import Mathlib
import Definitions.Def_MonoApport_Flow_Setting

namespace MonoApport.Flow

/-- Theorem 3 (p. 21): for every instance `(p, H)`, `𝒜(p, H) = {A(x, H) : x ∈ ℰ(p, Φ(p, H))}`,
as sets of real vectors. -/
theorem theorem_3 {n : ℕ} (p : Fin n → ℕ) (hp : IsPop p) (H : ℕ) (hH : 0 < H) :
    (fun y : Fin n → ℕ => fun i => (y i : ℝ)) '' calA p H =
      (fun x => A x H) '' calE p (Phi p H) := by sorry

end MonoApport.Flow
