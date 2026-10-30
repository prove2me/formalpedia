-- Prove2me | Theorems.Thm_MonoApport_Flow_balinski_young
-- name    : MonoApport.Flow.balinski_young
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:39:27.352378+00:00
-- url     : https://prove2.me/theorems/be5d7709-682c-440c-be7a-be2370c9efa0
-- title:
--   §C.4, p. 42 — Balinski–Young: f is house-monotone and quota-compliant iff each seat H + 1 goes to a state of ℒ(p, H, f(p, H)) ∩ 𝒰(p, H, f(p, H))
-- statement:
--   Let $f$ assign to every instance $(p,H)$ (populations $p\in\mathbb N^n$, positive house size $H$) a vector $f(p,H)\in\mathbb N_0^n$, and set $f(p,0)=0$. For a vector $y$ with $\sum_i y_i=H$ let $k^\star(p,H,y)$ be the least $k\ge1$ with $\sum_{i:\lfloor p_i(H+k)/P\rfloor>y_i}(\lfloor p_i(H+k)/P\rfloor-y_i)\ge k$, and
--   $$\mathcal L(p,H,y)=\Big\{i:\Big\lfloor\tfrac{p_i}{P}(H+k^\star(p,H,y))\Big\rfloor>y_i\Big\},\qquad \mathcal U(p,H,y)=\Big\{i:\tfrac{p_i}{P}(H+1)>y_i\Big\}.$$
--
--   **Characterization (Balinski and Young, as summarized in §C.4).** $f$ is a house-monotone and quota-compliant solution if and only if, for every $p$ and every house size $H\ge0$, there is one state
--   $$i\in\mathcal L(p,H,f(p,H))\cap\mathcal U(p,H,f(p,H))$$
--   with $f_i(p,H+1)=f_i(p,H)+1$ and $f_j(p,H+1)=f_j(p,H)$ for every $j\ne i$.
--
--   The characterization describes every house-monotone, quota-compliant solution as a seat-by-seat construction; the network-flow characterization (Theorem 3) is proved by matching this construction with the extreme points of (1)–(4).
--
--   **Formalization Note.** The convention $f(p,0)=0$ is `ext f p 0 = 0`, so the case $H=0$ is the assignment of the first seat. $\mathcal L$ and $\mathcal U$ are evaluated at the real cast of $f(p,H)$. "A solution" includes the requirement $\sum_i f_i(p,H)=H$ (`IsSolution`), which on the right-hand side follows from the construction.
--
--   Differences from the source:
--   - encoding: a solution is an apportionment method f with |f(p, H)| = 1, mapping each instance (p, H) ∈ ℕⁿ × ℕ to a vector of ℕ₀ⁿ with Σᵢ xᵢ = H → f : Solution, one function ∀ n, (Fin n → ℕ) → ℕ → (Fin n → ℕ) defined on vectors of every length, with IsSolution f asserting Σᵢ f(p, H)ᵢ = H on every instance; reason: single-valuedness is carried by the type; values of f off the instances (n = 0, a zero population, H = 0) are never used
--   - encoding: house monotonicity (c): for H₁ < H₂ < H₃ and every y ∈ f(p, H₂) there exist x ∈ f(p, H₁), z ∈ f(p, H₃) with x ≤ y ≤ z → HouseMonotone f: for all house sizes 0 < H₁ < H₂ < H₃, f(p, H₁) ≤ f(p, H₂) and f(p, H₂) ≤ f(p, H₃) componentwise; reason: for a solution every outcome is a singleton, so the existential quantifiers collapse to the unique values
--   - encoding: f(p, 0) = 0, and for every house size H the step from f(p, H) to f(p, H + 1) → ext f p H := if H = 0 then 0 else f p H, and the step from ext f p H to ext f p (H + 1) for every H : ℕ, H = 0 included; reason: the paper's convention f(p, 0) = 0 of the same sentence; methods are defined only on positive house sizes
--   - encoding: ℒ(p, H, y) and 𝒰(p, H, y) for an integer vector y with Σᵢ yᵢ = H, with k* a minimum → calL and calU applied to the real cast of ext f p H, with kStar an sInf on ℕ; reason: the cast is exact; on the vectors that occur the minimum exists, so sInf is the minimum
-- source:
--   Cembrano, Correa, Schmidt-Kraepelin, Tsigonias-Dimitriadis & Verdugo, New Combinatorial Insights for Monotone Apportionment, arXiv:2410.23869v1, §C.4, p. 42 (summary of Balinski and Young [1979, 2010])

import Mathlib
import Definitions.Def_MonoApport_Flow_Setting

namespace MonoApport.Flow

/-- The Balinski–Young characterization as summarized in §C.4 (p. 42): `f` is a house-monotone
and quota-compliant solution if and only if, with `f(p, 0) = 0`, for every house size `H ≥ 0`
the seat `H + 1` goes to one state `i ∈ ℒ(p, H, f(p, H)) ∩ 𝒰(p, H, f(p, H))` and every other
state keeps its seats. -/
theorem balinski_young (f : Solution) :
    (IsSolution f ∧ HouseMonotone f ∧ QuotaCompliant f) ↔
      ∀ (n : ℕ) (p : Fin n → ℕ), IsPop p → ∀ H : ℕ,
        ∃ i ∈ calL p H (fun j => (ext f p H j : ℝ)) ∩ calU p H (fun j => (ext f p H j : ℝ)),
          ext f p (H + 1) = ext f p H + Pi.single i 1 := by sorry

end MonoApport.Flow
