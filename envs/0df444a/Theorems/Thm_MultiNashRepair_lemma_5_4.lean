-- Prove2me | Theorems.Thm_MultiNashRepair_lemma_5_4
-- name    : MultiNashRepair.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:32:46.689495+00:00
-- url     : https://prove2.me/theorems/d9f08cbb-a0b2-473f-8e0c-4beb935fddae
-- title:
--   Lemma 5.4 — raw repair (5.19)–(5.21) and corrected retention (5.22)–(5.23)
-- statement:
--   Let $x$ be a mixed profile with mixed deviations $b_i$, $\gamma$ a probability vector with $0\le t\gamma_i<1$, $y_i=(1-t\gamma_i)x_i+t\gamma_ib_i$, and reverse budgets $\delta_i\ge0$ with $\sum_i\delta_i=1-\rho<1$; let $\tilde x$ be the raw profile of the reverse sweep (any pure best responses $e^{\mathrm{rev}}_i$). Put $C_{\mathrm{raw}}=\rho\prod_i(1-t\gamma_i)$, $\alpha_i=t\gamma_i/(1-t\gamma_i)$, $\omega_i=\delta_i/P_i$ with $P_i=1-\sum_{j\le i}\delta_j$, $S_{\mathrm{ev}}=\sum_i(\alpha_i+\omega_i)$, $d^0_i=d_{i,b_i}(x)$, $d_{ij}(y_j)=d_{i,b_i}(x[j\leftarrow y_j])$, $q=1-\mathrm{Reg}(x)$, $\varsigma=mq$, and let the stored generations $s$ have the retained event law of Lemma 5.2.
--
--   1. For every player $i$,
--   $$q_i(\tilde x)\ge C_{\mathrm{raw}}q+\delta_i+C_{\mathrm{raw}}\alpha_i(1+S_{\mathrm{ev}})+C_{\mathrm{raw}}S_{\mathrm{ev}}\sum_sA^{(s)}\alpha^{(s)}_i-e^{\mathrm{new}}_i-\sum_se^{(s)}_i\qquad(5.19)$$
--   with $e^{\mathrm{new}}_i=C_{\mathrm{raw}}\alpha_i\bigl[d^0_i+\alpha_i+\omega_i+\sum_{j\ne i}\alpha_jd_{ij}(b_j)+\sum_{j\ne i}\omega_jd_{ij}(e^{\mathrm{rev}}_j)\bigr]$ (5.20) and $e^{(s)}_i=C_{\mathrm{raw}}A^{(s)}\alpha^{(s)}_i\bigl[\alpha_i+\omega_i+\sum_{j\ne i}\alpha_jd^{(s)}_{ij}(b_j)+\sum_{j\ne i}\omega_jd^{(s)}_{ij}(e^{\mathrm{rev}}_j)\bigr]$ (5.21).
--   2. If $C_{\mathrm{raw}}t(1+S_{\mathrm{ev}})\ge\beta$, $C_{\mathrm{raw}}S_{\mathrm{ev}}\ge\nu$ and $\delta_i=D/m-\beta\gamma_i-\nu h_i$ with $D=1-\rho+\beta+\nu H$, then the frozen deficits $e^{\mathrm{cor}}_i=(C_{\mathrm{raw}}q+D/m-q_i(\tilde x))_+$ have total $E\le\sum_i\bigl(e^{\mathrm{new}}_i+\sum_se^{(s)}_i\bigr)$, and the forward correction (any pure best responses) gives
--   $$\varsigma^+\ge\frac{C_{\mathrm{raw}}\varsigma+D}{1+E}\qquad(5.22).$$
--   3. If moreover $\widehat C=C_{\mathrm{raw}}/(1+E)\ge c$, certificate thinning keeps every old generation with mass multiplied by $c$ and adds the new generation $(x,b,\gamma,t)$ with mass $c$ (5.23), and $\varsigma^+\ge c\varsigma+D-DE$.
--
--   Differences from the source:
--   - reading: the retained event law of Lemma 5.2 (disjoint events on an augmented probability space) → `CertLaw` (pointwise domination of the laws, with one domination per opponent override); reason: Lemma 5.2 in measure form; the proofs use only these dominations
--   - generalization: the fixed controls $t,\rho,\beta,\nu,c$ of (5.3)–(5.4) → any reals with $0\le t\gamma_i<1$, $\rho>0$, $\beta\ge0$, $\nu\ge0$, $c>0$; reason: the paper's controls satisfy these; the item specializes to them
--   - generalization: the best responses selected by the algorithm → any pure best responses in both sweeps; reason: the sweeps' best responses are arbitrary ties; contains the algorithm's choice
--   - reading: (5.23) $H^+=c(H+t)$, $h^+=c(h+t\gamma)$ by certificate thinning → the certificate law of the corrected profile with old masses times $c$ and the new generation of mass $c$; reason: the identities are the algorithm's update (3.11); the content of the thinning is the retained law
--   - generalization: game with rational payoffs in $[0,1]$ → any real game with payoffs in $[0,1]$ (`BoundedGame`); reason: the proof uses only $0\le u_i\le1$; contains the paper's rational games
-- source:
--   J. Tang, S. Ding, C. Fang, Breaking the One-Player Extension Barrier: History-Aware Repair for Multiplayer Approximate Nash Equilibria, arXiv:2611.06076 (preprint; held version, sha256 34b911ed…5c14), Lemma 5.4, (5.19)–(5.23), p.25; setting and odds (5.17), p.24

import Mathlib
import Definitions.Def_NashAmplification_Filtering_Model
import Definitions.Def_MultiNashRepair_Generation
import Definitions.Def_MultiNashRepair_Sweeps

open NashAmplification.Filtering (Mixed Utility Tuple BoundedGame)
open Finset

namespace MultiNashRepair

/-- **Lemma 5.4 (Raw Repair and Corrected Retention)** (Tang, Ding, Fang, arXiv:2611.06076,
Lemma 5.4, (5.19)–(5.23), p.25; setting and odds (5.17), p.24).

Setting (p.24): `x` a mixed profile, `b_i` mixed deviations, `γ` an activation law with
`0 ≤ t γ_i < 1`, `y_i = (1 − tγ_i) x_i + tγ_i b_i`, reverse budgets `δ_i ≥ 0` with
`Σ_i δ_i = 1 − ρ < 1`, `P_i = 1 − Σ_{j≤i} δ_j`, the raw profile `x̃` of the reverse sweep with any
pure best responses `e^{rev}_i`, `C_raw = ρ Π_i (1 − tγ_i)`, odds `α_i = tγ_i/(1 − tγ_i)`,
`ω_i = δ_i/P_i`, `S_ev = Σ_i (α_i + ω_i)` (5.17), and stored generations `s` with the retained
event law of Lemma 5.2, masses `A^{(s)}` and odds `α^{(s)}_i`.

1. (5.19) `q_i(x̃) ≥ C_raw q + δ_i + C_raw α_i (1 + S_ev) + C_raw S_ev Σ_s A^{(s)} α^{(s)}_i
   − e^{new}_i − Σ_s e^{(s)}_i` with the errors (5.20), (5.21).
2. If `C_raw t (1 + S_ev) ≥ β`, `C_raw S_ev ≥ ν` and `δ_i = D/m − βγ_i − ν h_i` with
   `D = 1 − ρ + β + ν H`, then the frozen deficits `e^{cor}_i = (C_raw q + D/m − q_i(x̃))_+` have
   total `E ≤ Σ_i (e^{new}_i + Σ_s e^{(s)}_i)`, and the forward correction (3.10), with any pure
   best responses, gives `ς⁺ ≥ (C_raw ς + D)/(1 + E)` (5.22).
3. If moreover `Ĉ = C_raw/(1 + E) ≥ c`, certificate thinning (Lemma 5.2 (C5)) retains every old
   generation with mass multiplied by `c` and adds the new generation `(x, b, γ, t)` with mass `c`,
   which gives (5.23), and `ς⁺ ≥ cς + D − DE`.

**Formalization Note.** "The retained event law" is `CertLaw` (Lemma 5.2 in measure form); its
conclusion in 3 is the content of (5.23), whose identities `H⁺ = c(H + t)`, `h⁺ = c(h + tγ)` are
the algorithm's update. The parameters `t, ρ, β, ν, c` are any reals with `0 < ρ`, `0 ≤ β`,
`0 ≤ ν`, `0 < c`; the paper's controls (5.3)–(5.4) satisfy these. `q = 1 − Reg(x)`,
`ς = m q`. -/
theorem lemma_5_4 {m : ℕ} {n : Fin m → ℕ} (hm : 1 ≤ m) (hn : ∀ i, 0 < n i)
    (u : Utility n) (hu : BoundedGame u) (x : Mixed n) (hx : AGT.IsMixedProfile x)
    (b : Mixed n) (hb : AGT.IsMixedProfile b) (γ : Fin m → ℝ) (hγ : AGT.IsLottery γ)
    (t ρ β ν c : ℝ) (htγ : ∀ i, 0 ≤ t * γ i ∧ t * γ i < 1) (hρ : 0 < ρ) (hβ : 0 ≤ β)
    (hν : 0 ≤ ν) (hc : 0 < c)
    (δ : Fin m → ℝ) (hδ0 : ∀ i, 0 ≤ δ i) (hδ1 : ∑ i, δ i = 1 - ρ)
    (gs : List (Gen n)) (hgs : ∀ g ∈ gs, GenLegal g) (hcert : CertLaw x gs)
    (h : Fin m → ℝ) (hh : ∀ i, h i = (gs.map fun g => g.A * g.t * g.γ i).sum)
    (arev acor : (i : Fin m) → Fin (n i))
    (hrev : IsRevBR u (actY x b t γ) δ arev) :
    let y := actY x b t γ
    let xt := revSweep y δ arev
    let Craw := ρ * ∏ i, (1 - t * γ i)
    let α : Fin m → ℝ := fun i => t * γ i / (1 - t * γ i)
    let ω : Fin m → ℝ := fun i => δ i / (1 - ∑ j ∈ univ.filter (· ≤ i), δ j)
    let Sev := ∑ i, (α i + ω i)
    let d0 : Fin m → ℝ := fun i => deficitMix u x i (b i)
    let dij : (i j : Fin m) → (Fin (n j) → ℝ) → ℝ :=
      fun i j yj => deficitMix u (Function.update x j yj) i (b i)
    let enew : Fin m → ℝ := fun i => Craw * α i * (d0 i + α i + ω i
      + ∑ j ∈ univ.erase i, α j * dij i j (b j)
      + ∑ j ∈ univ.erase i, ω j * dij i j (ePure (arev j)))
    let eold : Fin m → ℝ := fun i => (gs.map fun g => Craw * g.A * g.odds i * (α i + ω i
      + ∑ j ∈ univ.erase i, α j * g.col u i j (b j)
      + ∑ j ∈ univ.erase i, ω j * g.col u i j (ePure (arev j)))).sum
    let oldMass : Fin m → ℝ := fun i => (gs.map fun g => g.A * g.odds i).sum
    let H := ∑ i, h i
    let D := 1 - ρ + β + ν * H
    let ecor : Fin m → ℝ := corrDef u (scaled u x) Craw D xt
    let E := ∑ i, ecor i
    let xp := fwdSweep xt ecor acor
    (∀ i, Craw * q u x + δ i + Craw * α i * (1 + Sev) + Craw * Sev * oldMass i - enew i
        - eold i ≤ qi u xt i) ∧
    (β ≤ Craw * t * (1 + Sev) → ν ≤ Craw * Sev → (∀ i, δ i = D / m - β * γ i - ν * h i) →
      IsFwdBR u xt ecor acor →
      E ≤ ∑ i, (enew i + eold i) ∧ (Craw * scaled u x + D) / (1 + E) ≤ scaled u xp ∧
      (c ≤ Craw / (1 + E) →
        CertLaw xp (gs.map (fun g => { g with A := c * g.A }) ++ [⟨x, b, γ, t, c⟩]) ∧
        c * scaled u x + D - D * E ≤ scaled u xp)) := by sorry

end MultiNashRepair
