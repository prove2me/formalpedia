-- Prove2me | Theorems.Thm_MatMulDS_theorem_A_7
-- name    : MatMulDS.theorem_A_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:08:52.185522+00:00
-- url     : https://prove2.me/theorems/aec2ee8c-ca8a-4eb7-aded-5a647b0ffbb5
-- title:
--   Theorem A.7 — bilinear data structures from a base identity (corrected: $1+\cdots$ in $P_{\mathrm{pre}}+T_{\mathrm{box}}$; rational weights for uniformity)
-- statement:
--   Fix a block tensor with an identity, a private map and a compatible weight function, a distribution $\pi$ on $O$ with rational values, uniform within each block, with $\mathrm{len}(\pi)>0$, a threshold $0\le\eta_{\mathrm{pre}}\le\mu$ and $\theta\ge0$, and let $\nu,E,\Gamma,Q$ be the rates (A.19).
--
--   1. For every sufficiently large admissible $L$, there is a bilinear data structure for $N_0\times D_0$ and $D_0\times N_0$ matrices with
--   $$T_{\mathrm{enc}}\le\tilde O(N_0D_0^E),\quad P_{\mathrm{pre}}+T_{\mathrm{box}}\le\tilde O(N_0^2D_0^{-\Gamma}),\quad T_{\mathrm{query}}\le\tilde O(D_0^Q),$$
--   whose query circuits can be constructed in $\tilde O(D_0^Q)$ time.
--   2. For every fixed $\Delta<1/\nu$ and $2\le D\le N^\Delta$, there is a bilinear data structure for $N\times D$ and $D\times N$ matrices with
--   $$T_{\mathrm{enc}}\le\tilde O(ND^E),\quad P_{\mathrm{pre}}+T_{\mathrm{box}}\le\tilde O(N^2D^{-\Gamma}),\quad T_{\mathrm{query}}\le\tilde O(D^Q).$$
--   Consequently, arbitrary $A,B$ admit a deterministic data structure with preprocessing time and space $\tilde O(ND^E+N^2D^{-\Gamma})$ and worst-case query time $\tilde O(D^Q)$ for adaptive queries, and any $M$ entries of $AB$ can be computed in $\tilde O(ND^E+N^2D^{-\Gamma}+MD^Q)$ time.
--
--   The $\tilde O$ hides factors polynomial in $L=O(\log D)$. This reduces the data structures to four rates.
--
--   Differences from the source:
--   - correction: $P_{\mathrm{pre}}+T_{\mathrm{box}}\le\tilde O(N_0^2D_0^{-\Gamma})$, and likewise in (ii) → $\tilde O(1+N_0^2D_0^{-\Gamma})$, and likewise in (ii); reason: false as printed: with the five-term identity, weights $\mathrm{wt}+1$, $\pi$ uniform, $\eta_{\mathrm{pre}}=0$, $\theta=2$, the bound tends to $0$ while $P_{\mathrm{pre}}\ge1$; nothing changes when the bound is at least $1$
--   - reading: uniform circuits and the machine consequence, with weights and threshold "fixed" → those two clauses take $\mathrm{wt}$, $\eta_{\mathrm{pre}}$ rational; the circuit bounds hold for all reals; reason: the source does not say how a program reads a real threshold; its construction computes the light strings, which determine $\lfloor2L\eta_{\mathrm{pre}}\rfloor$ for all $L$ (Lemma A.6), so no fixed finite program follows it for an uncomputable threshold; the source only uses exact decimals
--   - encoding: $\Delta<1/\nu$ → $\Delta\nu<1$; reason: the same for $\nu>0$; for $\nu=0$ the source's $1/\nu$ is infinite while Lean's $1/0$ is $0$
--   - reading: $N_0,D_0$ with (A.12) → two-sided bounds, with $N_0=\mathrm{Row}K_{\mathrm{block}}\tilde c$ and $D_0=\tilde m^2$; reason: as in Lemma A.4
--   - encoding: $\tilde O$ → $C(L+1)^c$ in (i), $C(\log D+1)^c$ in (ii), fixed before $L$ and before $N,D$; reason: the source: "factors polynomial in $L=O(\log D)$"
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), Theorem A.7, eq. (A.19), p.77 (PDF p.79)

import Mathlib
import Definitions.Def_MatMulDS_IdentityData
import Definitions.Def_MatMulDS_BlockSeq
import Definitions.Def_MatMulDS_UniformFamily

set_option autoImplicit false

namespace MatMulDS

variable {I K J B P : Type} [Fintype I] [Fintype K] [Fintype J] [Fintype B] [Fintype P]
  [DecidableEq I] [DecidableEq K] [DecidableEq J] [DecidableEq B] [DecidableEq P]

/-- **Theorem A.7 (Bilinear Data Structures from a Base Identity), p.77** (Alman, Nogler, Vassilevska Williams, STOC 2027 submission,
held file sha256 6c5a1c16…). Fix a block tensor with an identity, a private map and a compatible weight function, a distribution `π` on `O`
with rational values that is uniform within each block and has `len(π) > 0`, a threshold `0 ≤ η_pre ≤ µ`, a parameter `θ ≥ 0`, and the rates
`ν, E, Γ, Q` of (A.19).
(i) For every sufficiently large admissible `L`, there is a bilinear data structure for `N0 × D0` and `D0 × N0` matrices with
`Tenc ≤ Õ(N0 D0^E)`, `Ppre + Tbox ≤ Õ(N0² D0^{−Γ})`, `Tquery ≤ Õ(D0^Q)`, whose query circuits can be constructed in `Õ(D0^Q)` time.
(ii) For every fixed `Δ < 1/ν` and `2 ≤ D ≤ N^Δ`, there is a bilinear data structure for `N × D` and `D × N` matrices with
`Tenc ≤ Õ(N D^E)`, `Ppre + Tbox ≤ Õ(N² D^{−Γ})`, `Tquery ≤ Õ(D^Q)`. Consequently, arbitrary `A`, `B` admit a deterministic data structure with
preprocessing time and space `Õ(N D^E + N² D^{−Γ})` and worst-case query time `Õ(D^Q)` for adaptive queries, and any `M` entries of `AB` can be
computed in `Õ(N D^E + N² D^{−Γ} + M D^Q)` time. The `Õ` hides factors polynomial in `L = O(log D)`.

**Formalization Note.**
* `Õ` is `C (L+1)^c` in (i) and `C (log D + 1)^c` in (ii), with `C`, `c` fixed before `L` and before `N`, `D`.
* In (i), `N0 = Row(π) Kblock(π) C̃ol(π)` and `D0 = M̃id(π)²` as in Lemma A.4, with (A.12).
* `Ppre + Tbox` is bounded by `Õ(1 + N0² D0^{−Γ})`, and likewise in (ii). As printed the bound fails when no string is light and `f < 0`: `N0² D0^{−Γ}`
  then tends to `0` while `Ppre ≥ 1` (see the differences).
* Uniformity and the machine consequence take `wt` and `η` rational: the printed construction computes the light strings, which a fixed finite program cannot do for an uncomputable threshold (see the differences).
* `Δ < 1/ν` is `Δ ν < 1`, the same condition for `ν > 0`. For `ν = 0` the source's `1/ν` is infinite, and Lean's `1/0 = 0` would be wrong. -/
theorem theorem_A_7 (F : Type) [Field F] [CharZero F] [DecidableEq F] (T : BlockTensor I K J B)
    (D : IdentityData I K J P) (hD : D.Computes T) (ρ : T.Out → P) (hρ : D.IsPrivateMap T ρ)
    (wt : P → ℝ) (hwt : D.IsCompatible T ρ wt) (π : I × J → ℚ) (hπ : IsBlockDistribution T π)
    (hlen : 0 < lenPi T π) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ mu π ρ wt) (θ : ℝ) (hθ : 0 ≤ θ) :
    let f := fRate wt θ η
    let ξ := xiRate D π ρ wt η
    let ν := nuRate T π
    let E := eRate T P π
    let Γ := gammaRate T π f
    let Q := qRate T π ξ
    -- (i) one tile
    (∃ (L₀ c : ℕ) (C : ℝ) (N0 D0 : ℕ → ℕ)
       (ds : ∀ x : {L : ℕ // L₀ ≤ L ∧ IsAdmissible T π L}, BilinearDS F (N0 x.1) (D0 x.1)),
      0 < C ∧
      (∀ x : {L : ℕ // L₀ ≤ L ∧ IsAdmissible T π L},
        let L := x.1
        (∃ cc m : ℕ, N0 L = rowCount T π L * Kblock T π L * cc ∧ D0 L = m ^ 2) ∧
        Real.exp (L * entropy T π) / ((L : ℝ) + 1) ^ c ≤ (N0 L : ℝ) ∧
        (N0 L : ℝ) ≤ Real.exp (L * entropy T π) ∧
        Real.exp (2 * L * lenPi T π) / ((L : ℝ) + 1) ^ c ≤ (D0 L : ℝ) ∧
        (D0 L : ℝ) ≤ Real.exp (2 * L * lenPi T π) ∧
        ((ds x).Tenc : ℝ) ≤ C * ((L : ℝ) + 1) ^ c * ((N0 L : ℝ) * (D0 L : ℝ) ^ E) ∧
        (((ds x).Ppre + (ds x).Tbox : ℕ) : ℝ) ≤
          C * ((L : ℝ) + 1) ^ c * (1 + (N0 L : ℝ) ^ 2 * (D0 L : ℝ) ^ (-Γ)) ∧
        ((ds x).Tquery : ℝ) ≤ C * ((L : ℝ) + 1) ^ c * (D0 L : ℝ) ^ Q) ∧
      ((∀ p, ∃ q : ℚ, wt p = q) → (∃ q : ℚ, η = q) →
        UniformFamily (fun x : {L : ℕ // L₀ ≤ L ∧ IsAdmissible T π L} => N0 x.1) (fun x => D0 x.1) ds
          (fun x => [(x.1 : ℤ)]) (fun x => x.1))) ∧
    -- (ii) one middle block
    (∀ Δ : ℝ, Δ * ν < 1 →
      ∃ (c : ℕ) (C : ℝ)
        (ds : ∀ x : {x : ℕ × ℕ // 1 ≤ x.1 ∧ 2 ≤ x.2 ∧ (x.2 : ℝ) ≤ (x.1 : ℝ) ^ Δ},
          BilinearDS F x.1.1 x.1.2),
        0 < C ∧
        (∀ x : {x : ℕ × ℕ // 1 ≤ x.1 ∧ 2 ≤ x.2 ∧ (x.2 : ℝ) ≤ (x.1 : ℝ) ^ Δ},
          let N : ℝ := (x.1.1 : ℝ)
          let Dm : ℝ := (x.1.2 : ℝ)
          ((ds x).Tenc : ℝ) ≤ C * (Real.log Dm + 1) ^ c * (N * Dm ^ E) ∧
          (((ds x).Ppre + (ds x).Tbox : ℕ) : ℝ) ≤ C * (Real.log Dm + 1) ^ c * (1 + N ^ 2 * Dm ^ (-Γ)) ∧
          ((ds x).Tquery : ℝ) ≤ C * (Real.log Dm + 1) ^ c * Dm ^ Q) ∧
        ((∀ p, ∃ q : ℚ, wt p = q) → (∃ q : ℚ, η = q) →
          UniformFamily (fun x : {x : ℕ × ℕ // 1 ≤ x.1 ∧ 2 ≤ x.2 ∧ (x.2 : ℝ) ≤ (x.1 : ℝ) ^ Δ} => x.1.1)
            (fun x => x.1.2) ds (fun x => inputWords x.1.1 x.1.2) (fun x => Nat.clog 2 (x.1.1 + 1)) ∧
          ∃ (O : MatroidSensOracle.AOracle) (cs : List F) (K' : ℕ) (C' : ℝ) (c' : ℕ),
            0 < C' ∧
            IsMatMulOracle O cs K' (fun N Dm => 2 ≤ Dm ∧ (Dm : ℝ) ≤ (N : ℝ) ^ Δ)
              (fun N Dm => C' * (Real.log Dm + 1) ^ c' * ((N : ℝ) * (Dm : ℝ) ^ E + (N : ℝ) ^ 2 * (Dm : ℝ) ^ (-Γ)))
              (fun _ Dm => C' * (Real.log Dm + 1) ^ c' * (Dm : ℝ) ^ Q) ∧
            ∀ (N Dm : ℕ), 1 ≤ N → 2 ≤ Dm → (Dm : ℝ) ≤ (N : ℝ) ^ Δ →
            ∀ (A : Matrix (Fin N) (Fin Dm) F) (B' : Matrix (Fin Dm) (Fin N) F) (w : ℕ),
              K' * Nat.clog 2 (N + 1) + K' ≤ w →
              ∀ qs : List (Fin N × Fin N),
                AnswersListWithin O cs w A B' qs
                  (C' * (Real.log Dm + 1) ^ c' *
                    ((N : ℝ) * (Dm : ℝ) ^ E + (N : ℝ) ^ 2 * (Dm : ℝ) ^ (-Γ) +
                      (qs.length : ℝ) * (Dm : ℝ) ^ Q)))) := by sorry

end MatMulDS
