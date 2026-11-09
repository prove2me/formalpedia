-- Prove2me | Theorems.Thm_MultiNashRepair_lemma_5_3
-- name    : MultiNashRepair.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:32:17.241573+00:00
-- url     : https://prove2.me/theorems/59002b35-59f6-4b92-89a2-12efa3a2c896
-- title:
--   Lemma 5.3 — finite historical overlap (5.16)
-- statement:
--   Let $x$ be a mixed profile of an $m$-player game with payoffs in $[0,1]$ and $\varsigma=m(1-\mathrm{Reg}(x))$. Let $\lambda$ be a probability vector on players and $b_i$ mixed deviations with
--   $$\sum_i\lambda_i\,d_{i,b_i}(x[j\leftarrow y_j])<\frac{\varsigma+\mu}{m}\quad\text{for every }j\text{ and mixed }y_j\qquad(5.11).$$
--   Let the stored repair generations be legal, satisfy the column certificate (5.15) with constant $L_{\mathrm{col}}\ge0$, and have the retained event law of Lemma 5.2. Let $h_i=\sum_sA^{(s)}t^{(s)}\gamma^{(s)}_i\ge0$, $H=\sum_ih_i$, $Y\ge0$ and $mh_i\le H+Y$ for all $i$. With $\pi_i=m\lambda_i$, $r=\max_i\pi_i-1$, $v_i=mh_i-H$ and $H\psi=\sum_i\lambda_iv_i$, there is $\vartheta$ with
--   $$(1+r)(1-\vartheta)+H(1+\psi)<\varsigma+\mu,\qquad 0\le\vartheta\le\frac{H+Y+L_{\mathrm{col}}H}{m}\qquad(5.16).$$
--
--   Combined with (5.11) this yields the floor condition (5.26) that makes the tilted repair of Lemma 5.5 legal.
--
--   Differences from the source:
--   - generalization: an optimal rational dual certificate of a failed LP satisfying (5.11) → any probability vector $\lambda$ and mixed deviations $b$ satisfying (5.11); reason: the proof uses only (5.11); contains the paper's certificate
--   - reading: the retained event law of Lemma 5.2 (disjoint events on an augmented probability space) → `CertLaw` (pointwise domination of the laws, with one domination per opponent override); reason: Lemma 5.2 in measure form; the proofs use only these dominations
--   - encoding: $H(1+\psi)$ → $H+H\psi$ with $H\psi=\sum_i\lambda_iv_i$; reason: the paper's meaning, including at $H=0$ (p.23)
--   - encoding: the stored masses (5.13) → the hypothesis $h_i=\sum_sA^{(s)}t^{(s)}\gamma^{(s)}_i$ over the list of generations; reason: the paper's definition of $h_i$
--   - generalization: game with rational payoffs in $[0,1]$ → any real game with payoffs in $[0,1]$ (`BoundedGame`); reason: the proof uses only $0\le u_i\le1$; contains the paper's rational games
--   - generalization: $L_{\mathrm{col}}=9$ (fixed on p.15) → any $L_{\mathrm{col}}\ge0$; reason: the proof uses only (5.15) with constant $L_{\mathrm{col}}$; specializes to $L_{\mathrm{col}}=9$
-- source:
--   J. Tang, S. Ding, C. Fang, Breaking the One-Player Extension Barrier: History-Aware Repair for Multiplayer Approximate Nash Equilibria, arXiv:2611.06076 (preprint; held version, sha256 34b911ed…5c14), Lemma 5.3, (5.16), p.23; notation (5.13)–(5.15), pp.19, 23

import Mathlib
import Definitions.Def_NashAmplification_Filtering_Model
import Definitions.Def_MultiNashRepair_Generation

open NashAmplification.Filtering (Mixed Utility Tuple BoundedGame)
open Finset

namespace MultiNashRepair

/-- **Lemma 5.3 (Finite Historical Overlap)** (Tang, Ding, Fang, arXiv:2611.06076, Lemma 5.3,
(5.16), p.23; notation (5.13)–(5.15), pp.19, 23).

Let `x` be a mixed profile, `λ` a probability vector on players and `b_i` mixed deviations
satisfying (5.11): `Σ_i λ_i d_{i,b_i}(x[j ← y_j]) < (ς + µ)/m` for every `j` and mixed `y_j`, where
`ς = m(1 − Reg(x))`. Let the stored generations be legal, satisfy the column certificate (5.15)
with constant `Lcol ≥ 0`, and have the retained event law of Lemma 5.2. Let
`h_i = Σ_s A^{(s)} t^{(s)} γ^{(s)}_i ≥ 0`, `H = Σ_i h_i`, `Y ≥ 0` and `m h_i ≤ H + Y` for all `i`.
With `π_i = m λ_i`, `r = max_i π_i − 1`, `v_i = m h_i − H` and `Hψ = Σ_i λ_i v_i`,
`(1 + r)(1 − ϑ) + H(1 + ψ) < ς + µ` for some `0 ≤ ϑ ≤ (H + Y + Lcol H)/m` (5.16).

**Formalization Note.** "The retained event law of Lemma 5.2" is `CertLaw` (Lemma 5.2 in measure
form). `H(1 + ψ)` is written `H + Hψ`, which is also its meaning at `H = 0` (p.23). The lemma is
stated for every `(λ, b)` with (5.11), not only an optimal rational dual, and for every
`Lcol ≥ 0` (the paper applies it with `Lcol = 9`). -/
theorem lemma_5_3 {m : ℕ} {n : Fin m → ℕ} (hm : 1 ≤ m) (hn : ∀ i, 0 < n i)
    (u : Utility n) (hu : BoundedGame u) (x : Mixed n) (hx : AGT.IsMixedProfile x)
    (lam' : Fin m → ℝ) (b : Mixed n) (hlam : AGT.IsLottery lam') (hb : AGT.IsMixedProfile b)
    (mu : ℝ)
    (h511 : ∀ (j : Fin m) (y : Fin (n j) → ℝ), AGT.IsLottery y →
      ∑ i, lam' i * deficitMix u (Function.update x j y) i (b i) < (scaled u x + mu) / m)
    (gs : List (Gen n)) (hgs : ∀ g ∈ gs, GenLegal g) (hcert : CertLaw x gs)
    (Lcol : ℝ) (hL : 0 ≤ Lcol) (hcol : ColumnBound u gs Lcol)
    (h : Fin m → ℝ) (hh : ∀ i, h i = (gs.map fun g => g.A * g.t * g.γ i).sum)
    (hh0 : ∀ i, 0 ≤ h i) (Y : ℝ) (hY : 0 ≤ Y) (hmh : ∀ i, (m : ℝ) * h i ≤ ∑ j, h j + Y) :
    let H := ∑ i, h i
    let r := (⨆ i, (m : ℝ) * lam' i) - 1
    let Hψ := ∑ i, lam' i * ((m : ℝ) * h i - H)
    ∃ ϑ : ℝ, 0 ≤ ϑ ∧ ϑ ≤ (H + Y + Lcol * H) / m ∧
      (1 + r) * (1 - ϑ) + (H + Hψ) < scaled u x + mu := by sorry

end MultiNashRepair
