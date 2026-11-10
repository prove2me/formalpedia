-- Prove2me | Theorems.Thm_NearOptOWF_claim_4_8
-- name    : NearOptOWF.claim_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:12:42.049768+00:00
-- url     : https://prove2.me/theorems/cfec0968-ff1a-454a-8f90-5a3409e5f9c2
-- title:
--   Claim 4.8 — unsatisfiable $\varphi$: $\Pr_{G,y}[E] \ge 2^{n^{2\delta}-m} - 2^N\cdot 2^{-\lambda^{\Omega(1)}}$
-- statement:
--   Let $\varphi$ be an **unsatisfiable** circuit on $r \le N$ inputs, read on the first $r$ bits of $x \in \{0,1\}^N$. Let $G_k$ be circuits indexed by uniform keys $k$, and for each $k$ and $y \in \{0,1\}^m$ let $P_{k,y}$ be a circuit computing the planted function
--   $$
--   G_{\varphi,y}(x) = \begin{cases} G_k(x) & \varphi(x) = 0, \\ y & \varphi(x) = 1. \end{cases}
--   $$
--   Let $A(g, y)$ be any output distributions on $\{\perp\} \cup \{0,1\}^N$. Suppose that $A(G, y)$ outputs a pre-image in $G^{-1}(y)$ with probability at least $s$ over $k$ and $y \leftarrow \{0,1\}^m$, and that $A(G_k, y)$ and $A(P_{k,y}, y)$ are at most $\eta$-far for all $k, y$. Then, for $x \leftarrow A(G_{\varphi,y}, y)$ and the events $E_1 : G_{\varphi,y}(x) = y$ and $E_2 : \varphi(x) = 0$,
--   $$
--   \Pr_{G,y}[E_1 \wedge E_2] \ge s - \eta.
--   $$
--   With $s = 2^{n^{2\delta} - m}$ and $\eta = 2^N \cdot 2^{-\lambda^{c}}$ from Claim 4.7 this is the printed bound. Together with Claim 4.9 it separates satisfiable from unsatisfiable $\varphi$ by a factor of two, which the set lower-bound protocol (Theorem 3.2) turns into an AM protocol for unsatisfiability.
--
--   Differences from the source:
--   - generalization: the sampler A of Claim 4.7, the puncturable PRF G, and the bounds 2^{n^{2δ}−m} and 2^N·2^{-λ^{Ω(1)}} → any output distributions D(g, y), any key-indexed circuits G_k, any circuits P k y computing G_{φ,y}, a success hypothesis with parameter s and a functional-equivalence hypothesis with error η on the pairs (G_k, P k y); reason: the proof uses only these two properties; the printed claim is the instance s = 2^{n^{2δ}−m}, η = 2^N·2^{-λ^c}
--   - generalization: φ with n^δ input bits → φ with any r ≤ N input bits; reason: n^δ is not an integer; the instance in the proof is r = ⌈n^δ⌉
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Claim 4.8, p.16 (PDF p.18); G_{φ,y} and E = E₁ ∧ E₂ on the same page

import Mathlib
import Definitions.Def_LaconicBarrier_MCircuit
import Definitions.Def_KarpLiptonOM_Circuit_eval
import Definitions.Def_LaconicBarrier_coinAvg
import Definitions.Def_HybridXorLift_tvDist

namespace NearOptOWF

open LaconicBarrier

/-- **Claim 4.8** (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Claim 4.8, p.16 (PDF p.18); the planted function `G_{φ,y}` and the events
`E = E₁ ∧ E₂` on the same page), in the generality its proof uses: let `φ` be an **unsatisfiable**
circuit on `r ≤ N` inputs, read on the first `r` bits of `x ∈ {0,1}^N`; let `G_k` be circuits indexed by
uniform keys `k`, and for each `k` and `y ∈ {0,1}ᵐ` let `P k y` be a circuit computing the planted
function `G_{φ,y}(x) = G_k(x)` if `φ(x) = 0`, `= y` if `φ(x) = 1`; let `D(g, y)` be any output
distributions on `{⊥} ∪ {0,1}^N` (the sampler `A(g, y)`). If `A(G, y)` outputs a pre-image in
`G⁻¹(y)` with probability at least `s` (over `k` and `y`), and `A(G_k, y)` and `A(P k y, y)` are
`η`-far for all `k, y`, then for `x ← A(G_{φ,y}, y)`,
`Pr_{G,y}[E] ≥ s − η`, where `E₁ : G_{φ,y}(x) = y` and `E₂ : φ(x) = 0`.

With `s = 2^{n^{2δ}−m}` (Claim 4.7, success) and `η = 2^N · 2^{−λ^c}` (Claim 4.7, functional
equivalence) this is the printed bound `Pr_{G,y}[E] ≥ 2^{n^{2δ}−m} − 2^N · 2^{−λ^{Ω(1)}}`.

**Formalization Note** `φ` has `r` inputs in place of the paper's `n^δ`, which is not an integer. -/
theorem claim_4_8 (N m r a : ℕ) (hr : r ≤ N) (φ : KarpLiptonOM.Circuit r)
    (hφ : ∀ u : Fin r → Bool, φ.eval (List.ofFn u) = false)
    (Gs : (Fin a → Bool) → MCircuit N) (P : (Fin a → Bool) → (Fin m → Bool) → MCircuit N)
    (hP : ∀ (k : Fin a → Bool) (y : Fin m → Bool) (x : Fin N → Bool),
      (P k y).eval (List.ofFn x) =
        if φ.eval ((List.ofFn x).take r) = true then List.ofFn y else (Gs k).eval (List.ofFn x))
    (D : MCircuit N → List Bool → Option (Fin N → Bool) → ℝ)
    (hD0 : ∀ g y o, 0 ≤ D g y o) (hD1 : ∀ g y, ∑ o, D g y o = 1)
    (s η : ℝ)
    (hs : s ≤ coinAvg a fun k => coinAvg m fun y => ∑ z : Fin N → Bool,
      if (Gs k).eval (List.ofFn z) = List.ofFn y then D (Gs k) (List.ofFn y) (some z) else 0)
    (hη : ∀ k y, HybridXorLift.tvDist (D (Gs k) (List.ofFn y)) (D (P k y) (List.ofFn y)) ≤ η) :
    s - η ≤ coinAvg a fun k => coinAvg m fun y => ∑ z : Fin N → Bool,
      if (P k y).eval (List.ofFn z) = List.ofFn y ∧ φ.eval ((List.ofFn z).take r) = false then
        D (P k y) (List.ofFn y) (some z) else 0 := by sorry

end NearOptOWF
