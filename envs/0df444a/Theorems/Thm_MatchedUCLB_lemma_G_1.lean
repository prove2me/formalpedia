-- Prove2me | Theorems.Thm_MatchedUCLB_lemma_G_1
-- name    : MatchedUCLB.lemma_G_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:45:24.518603+00:00
-- url     : https://prove2.me/theorems/bc4da5b5-332b-45c4-bd93-c6eaa9a8fad5
-- title:
--   Lemma G.1 — calibration of $m$, $L$, $\mu$: class parameters, per-phase cost, phase gaps, $L\asymp\log(\Delta_0/\epsilon)$, dimension bound
-- statement:
--   Let $q=p+\nu$ with $p\ge2$, $0<\nu\le1$, let $a_q=(3q-2)/2$, $\kappa=H/\sigma$, and let $c_B,c_0,c_1,\eta$ be the constants of Lemma 4.5. For a constant $C_H>0$ define
--
--   $$
--   c_m=\Bigl(\frac{qc_B}{C_H}\Bigr)^{1/a_q},\quad \kappa_{p,\nu}=\Bigl(\frac{32}{c_m}\Bigr)^{a_q},\quad c_*=\frac{7c_1(1-\eta^q)}{2(1+c_0)},\quad c_L=\frac{1}{q\log(1/\eta)+\log(2/c_*)} .
--   $$
--
--   There is a constant $C>0$ such that for all $H,\sigma,\Delta_0>0$ with $\kappa\ge\kappa_{p,\nu}$ and $0<\epsilon\le c_*\Delta_0/2$, the choices $\tau_0=1$,
--
--   $$
--   \mu=\frac{\sigma}{qc_B},\qquad m=\bigl\lfloor c_m\kappa^{1/a_q}\bigr\rfloor,\qquad L=1+\Bigl\lfloor\frac{\log(c_*\Delta_0/(2\epsilon))}{q\log(1/\eta)}\Bigr\rfloor,\qquad n_m=\lfloor m/16\rfloor
--   $$
--
--   satisfy:
--
--   1. **(a)** $m\ge32$, $qc_B\mu=\sigma$, $C_H\mu m^{a_q}\le H$ and $n_m\ge\frac{c_m}{32}\kappa^{1/a_q}$;
--   2. **(b)** for every orthonormal phase frame and $0\le j<L$, $7\delta_j/D_{m,L}\ge c_*\eta^{qj}$; moreover $c_*\Delta_0\eta^{q(L-1)}\ge2\epsilon$ and $c_L\log(\Delta_0/\epsilon)\le L\le C\log(\Delta_0/\epsilon)$;
--   3. **(c)** with $K_{p,\nu}=2c_m\bigl(1+\frac{1}{q\log(1/\eta)}\bigr)$, $L(m+1)\le K_{p,\nu}(H/\sigma)^{2/(3q-2)}\log(\Delta_0/\epsilon)$.
--
--   Here $\delta_j$ and $D_{m,L}$ are those of the complete objective with these $\mu,m,L$ and $\tau_0=1$. The lemma turns the construction into the rates of Theorem 1.1: $n_m\asymp\kappa^{2/(3q-2)}$ calls per phase and $L\asymp\log(\Delta_0/\epsilon)$ phases, within the dimension budget.
--
--   **Formalization Note** Floors are natural-number floors and $n_m$ is natural division $m/16$.
--
--   Differences from the source:
--   - encoding: q = p + ν → a real binder q with the hypothesis hq : q = p + ν; reason: notation only; every instance has q = p + ν
--   - encoding: ⌊·⌋, n_m = ⌊m/16⌋, phase directions in ℝ^d → Nat.floor ⌊·⌋₊, natural division m / 16, phase frames in EuclideanSpace ℝ (Fin d); reason: the floored quantities are nonnegative, so ⌊·⌋₊ and natural division give the same integers; Lean convention for ℝ^d
--   - generalization: C_H the constant of Lemma 4.5 → every C_H > 0 (a theorem binder); reason: the calibration uses only C_H > 0; with the C_H of Lemma 4.5 it is the printed lemma
--   - reading: L ≍_{p,ν} log(Δ_0/ε) → c_L log(Δ_0/ε) ≤ L ∧ L ≤ C log(Δ_0/ε), with c_L as printed and ∃ C > 0 chosen before H, σ, Δ_0, ε; reason: two-sided comparison with constants depending only on p, ν (and C_H); the lemma defines c_L for the lower side
--   - reading: δ_j, D_{m,L} of the complete objective (frame implicit) → the bound 7δ_j/D_{m,L} ≥ c_*η^{qj} for every phase frame in every dimension; reason: by Lemma 4.5(d) D_{m,L} is the same for every frame, so the page leaves it implicit
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Lemma G.1, p.104

import Mathlib
import Definitions.Def_MatchedUCLB_objDelta
import Definitions.Def_MatchedUCLB_objGap
import Definitions.Def_MatchedUCLB_IsPhaseFrame
import Definitions.Def_MatchedUCLB_cB
import Definitions.Def_MatchedUCLB_c0
import Definitions.Def_MatchedUCLB_c1
import Definitions.Def_MatchedUCLB_aQ
import Definitions.Def_MatchedUCLB_eta

open scoped ContDiff Topology

namespace MatchedUCLB

/-- **Lemma G.1 (calibrating the oracle lower bound).** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, Lemma G.1, p.104: "Let `a_q = (3q−2)/2`
and `κ = H/σ`. With the constants of Lemma 4.5, define `c_m = (qc_B/C_H)^{1/a_q}`,
`κ_{p,ν} = (32/c_m)^{a_q}`, `c_* = 7c_1(1 − η^q)/(2(1 + c_0))`, `c_L = 1/(q log(1/η) + log(2/c_*))`.
Suppose `κ ≥ κ_{p,ν}` and `0 < ε ≤ c_*Δ_0/2`. Take `τ_0 = 1` and define `μ = σ/(qc_B)`,
`m = ⌊c_mκ^{1/a_q}⌋`, `L = 1 + ⌊log(c_*Δ_0/(2ε)) / (q log(1/η))⌋`. Then, with `n_m = ⌊m/16⌋`, (a) `m ≥ 32`,
`qc_Bμ = σ`, `C_Hμm^{a_q} ≤ H`, and `n_m ≥ (c_m/32)κ^{1/a_q}`. (b) For `0 ≤ j < L`,
`7δ_j/D_{m,L} ≥ c_*η^{qj}`, `c_*Δ_0η^{q(L−1)} ≥ 2ε`, `L ≍_{p,ν} log(Δ_0/ε)`. (c) For
`K_{p,ν} := 2c_m(1 + 1/(q log(1/η)))`, `L(m + 1) ≤ K_{p,ν}(H/σ)^{2/(3q−2)} log(Δ_0/ε)`."

**Formalization Note.** `q` is a separate real binder with the hypothesis `q = p + ν` (the matched order of the paper), so that every formula can be written in `q`. The lemma is stated for every `C_H > 0` (a generalization: the
paper's `C_H` of Lemma 4.5 is one such constant). Floors are `Nat.floor`, `n_m = m / 16` (natural
division). `δ_j = objDelta q μ m 1 j` and `D_{m,L} = objGap q μ L 1 v u` are those of the complete
objective with `τ_0 = 1`, for any phase frame in any dimension (by Lemma 4.5(d) `D_{m,L}` does not
depend on the frame). `L ≍_{p,ν} log(Δ_0/ε)` is `c_L log(Δ_0/ε) ≤ L ≤ C log(Δ_0/ε)` with `c_L` as
printed and a constant `C > 0` chosen before `H, σ, Δ_0, ε`. -/
theorem lemma_G_1 (p : ℕ) (hp : 2 ≤ p) (ν : ℝ) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (q : ℝ) (hq : q = (p : ℝ) + ν) (CH : ℝ) (hCH : 0 < CH) :
    let cm : ℝ := (q * cB q / CH) ^ (1 / aQ q)
    let cStar : ℝ := 7 * c1 q * (1 - eta q ^ q) / (2 * (1 + c0 q))
    let cL : ℝ := 1 / (q * Real.log (1 / eta q) + Real.log (2 / cStar))
    let Kpν : ℝ := 2 * cm * (1 + 1 / (q * Real.log (1 / eta q)))
    ∃ Cup : ℝ, 0 < Cup ∧
    ∀ H σ Δ₀ ε : ℝ, 0 < H → 0 < σ → 0 < Δ₀ → (32 / cm) ^ aQ q ≤ H / σ → 0 < ε →
      ε ≤ cStar * Δ₀ / 2 →
      let μ : ℝ := σ / (q * cB q)
      let m : ℕ := ⌊cm * (H / σ) ^ (1 / aQ q)⌋₊
      let L : ℕ := 1 + ⌊Real.log (cStar * Δ₀ / (2 * ε)) / (q * Real.log (1 / eta q))⌋₊
      -- (a)
      (32 ≤ m ∧ q * cB q * μ = σ ∧ CH * μ * (m : ℝ) ^ aQ q ≤ H ∧
        cm / 32 * (H / σ) ^ (1 / aQ q) ≤ ((m / 16 : ℕ) : ℝ)) ∧
      -- (b)
      ((∀ (d : ℕ) (v : ℕ → EuclideanSpace ℝ (Fin d)) (u : ℕ → Fin m → EuclideanSpace ℝ (Fin d)), IsPhaseFrame L v u →
          ∀ j : ℕ, j < L → cStar * eta q ^ (q * j) ≤ 7 * objDelta q μ m 1 j / objGap q μ L 1 v u) ∧
        2 * ε ≤ cStar * Δ₀ * eta q ^ (q * ((L : ℝ) - 1)) ∧
        cL * Real.log (Δ₀ / ε) ≤ L ∧ (L : ℝ) ≤ Cup * Real.log (Δ₀ / ε)) ∧
      -- (c)
      (L : ℝ) * (m + 1) ≤ Kpν * (H / σ) ^ (2 / (3 * q - 2)) * Real.log (Δ₀ / ε) := by sorry

end MatchedUCLB
