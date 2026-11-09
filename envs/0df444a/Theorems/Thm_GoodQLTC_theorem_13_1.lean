-- Prove2me | Theorems.Thm_GoodQLTC_theorem_13_1
-- name    : GoodQLTC.theorem_13_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:49:24.876143+00:00
-- url     : https://prove2.me/theorems/b53de3a2-6937-459c-b15e-9d7ea288919d
-- title:
--   Theorem 13.1: uniform product expansion of Reed–Solomon codes
-- statement:
--   Fix $t\ge4$ and $\tau\ge1$. For $1\le r\le t$ let $2\le q_1<\dots<q_r$ be powers of two with $q_r\le\tau q_1$, $\Omega_i=\{z:z^{q_i+1}=1\}$, $n_i=q_i+1$; fix $0<\epsilon\le1/2$, a finite field $F$ of characteristic two containing every $\Omega_i$, and $\rho=\rho(t,\tau,\epsilon)$ as in (13.1). For integers $u_i$ with $\epsilon\le u_i/n_i\le1-\epsilon$, the family $\{\mathrm{RS}_F(\Omega_i,u_i)\}_{i\in[r]}$ is universally $\rho$-product-expanding. The same constant $\rho$ works
--   1. for every nonempty subfamily,
--   2. for every independent choice of a code or its dual in each direction,
--   3. after arbitrary monomial changes of coordinates in the individual factors,
--
--   and all these families have collective $\rho$-product expansion over every extension $E/F$.
--
--   **Formalization Note** The statement is for every nonempty $I\subseteq[r]$, every choice of duals and every monomial change at once.
--
--   Differences from the source:
--   - encoding: Ω_i ⊆ k (k algebraically closed of characteristic two) and a finite field F ⊆ k containing every Ω_i → F any finite field of characteristic two in which each Ω_i = {z ∈ F : z^{q_i+1} = 1} has q_i + 1 elements; reason: embedding F in its algebraic closure gives the source's data, and conversely Ω_i(k) ⊆ F has q_i + 1 elements; same instances
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), Theorem 13.1, p.48 (PDF p.51); ρ from (13.1), p.48; C from the proof of Theorem 12.2, p.46

import Mathlib
import Definitions.Def_GoodQLTC_IsProductExpanding
import Definitions.Def_GoodQLTC_HasCollectiveExpansion
import Definitions.Def_GoodQLTC_dualCode
import Definitions.Def_GoodQLTC_rsCode
import Definitions.Def_GoodQLTC_rsRho

namespace GoodQLTC

universe u v

open Classical in
/-- **Theorem 13.1** (uniform product expansion of Reed–Solomon codes), Gay–Jeronimo,
arXiv:2609.20780 (held version), p.48. Fix an integer `t ≥ 4` and `τ ≥ 1`; for `1 ≤ r ≤ t` let
`2 ≤ q_1 < ⋯ < q_r` be powers of two with `q_r ≤ τ q_1`, `Ω_i := {z : z^{q_i+1} = 1}`,
`n_i := q_i + 1`; fix `0 < ε ≤ 1/2` and a finite field `F` containing every `Ω_i`; let `ρ` be as in
(13.1). For integers `u_i` with `ε ≤ u_i/n_i ≤ 1 − ε`, the family `{RS_F(Ω_i, u_i)}_{i∈[r]}` is
universally `ρ`-product-expanding. The same constant `ρ` works for every nonempty subfamily, for
every independent choice of a code or its dual in each direction, and after arbitrary monomial
changes of coordinates in the individual factors. All these families have collective
`ρ`-product expansion over every extension `E/F`.

**Formalization Note.** `F` is any finite field of characteristic two in which each
`Ω_i = {z ∈ F : z^{q_i+1} = 1}` has `q_i + 1` elements; this is the paper's `F ⊆ k` (`k`
algebraically closed of characteristic two) containing every `Ω_i`. `ρ = rsRho t τ ε` is the
explicit constant (13.1), `θ := ε/(2^t C)`, `ρ := (1/t)(θ/τ)^t`, with `C = C(t, τ)` from the proof of
Theorem 12.2 (p.46). The conclusion covers every nonempty `I ⊆ [r]`, every choice `dual i`, and
every monomial change `(σ_i, c_i)`. Extensions range over a universe `u`, coefficient spaces over
`v`. -/
theorem theorem_13_1 (t : ℕ) (ht : 4 ≤ t) (τ : ℝ) (hτ : 1 ≤ τ) (r : ℕ) (hr : 1 ≤ r)
    (hrt : r ≤ t) (q : Fin r → ℕ) (hpow : ∀ i, ∃ e : ℕ, q i = 2 ^ e)
    (hq1 : 2 ≤ q ⟨0, by omega⟩) (hmono : StrictMono q)
    (hqτ : (q ⟨r - 1, by omega⟩ : ℝ) ≤ τ * (q ⟨0, by omega⟩ : ℝ))
    (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (F : Type) [Field F] [Fintype F] [CharP F 2]
    (hΩ : ∀ i, Fintype.card {z : F // z ^ (q i + 1) = 1} = q i + 1)
    (u : Fin r → ℕ)
    (hu : ∀ i, ε ≤ (u i : ℝ) / ((q i : ℝ) + 1) ∧ (u i : ℝ) / ((q i : ℝ) + 1) ≤ 1 - ε)
    (I : Finset (Fin r)) (hI : I.Nonempty) (dual : Fin r → Bool)
    (σ : ∀ i : Fin r, Equiv.Perm {z : F | z ^ (q i + 1) = 1})
    (c : ∀ i : Fin r, {z : F | z ^ (q i + 1) = 1} → Fˣ) :
    IsUnivProductExpanding.{u} (rsRho t τ ε) (fun i : I =>
      monomialImage (σ i.1) (c i.1)
        (if dual i.1 then dualCode (rsCode {z : F | z ^ (q i.1 + 1) = 1} (u i.1))
          else rsCode {z : F | z ^ (q i.1 + 1) = 1} (u i.1))) ∧
    ∀ (E : Type u) [Field E] [Algebra F E],
      HasCollectiveExpansion.{u, v} E (rsRho t τ ε) (fun i : I =>
        monomialImage (σ i.1) (c i.1)
          (if dual i.1 then dualCode (rsCode {z : F | z ^ (q i.1 + 1) = 1} (u i.1))
            else rsCode {z : F | z ^ (q i.1 + 1) = 1} (u i.1))) := by sorry

end GoodQLTC
