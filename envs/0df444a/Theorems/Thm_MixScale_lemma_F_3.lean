-- Prove2me | Theorems.Thm_MixScale_lemma_F_3
-- name    : MixScale.lemma_F_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:08:41.707197+00:00
-- url     : https://prove2.me/theorems/978fc787-ddf1-4485-beb5-b51b6a907134
-- title:
--   Lemma F.3, p.37 — dyadic local estimates
-- statement:
--   Fix an integer $J\ge1$, $r>0$ and an integer $N_{\mathrm{der}}>\max\{J+1-r,0\}$. Let $g\in L^1(\mathbb R)$ be even, with $\hat g$ bounded on $[-2,2]$ and $|\partial_s^j\hat g(s)|\le C_j|s|^{-r-j}$ for $|s|\ge1$, $0\le j\le N_{\mathrm{der}}$. Then $g$ has a $C^J$ representative off zero, and for $0<|x|\le1$:
--
--   1. $|g(x)|\le C|x|^{r-1}$ if $0<r<1$;
--   2. $|g'(x)|\le C|x|^{-1}$ if $r=1$;
--   3. $|g^{(m)}(x)|\le C|x|^{r-1-m}$ for $r-1<m\le J$;
--   4. $|g(x)|\le C\log(e/|x|)$ if $r=1$.
--
--   If $r>1$, then $\hat g\in L^1$ and $g$ is bounded. Uniform symbol bounds give uniform constants. If $g=g_v$ is continuous as an $L^1$-valued function of $v$ in a compact interval, these representatives and their spatial derivatives through order $J$ are jointly continuous on compact sets separated from $x=0$.
--
--   This translates Fourier symbol bounds into the local spatial estimates needed by the chi-square integral.
--
--   Differences from the source:
--   - encoding: Uniform symbol bounds yield uniform constants → C chosen after J, r, N_der and the symbol constants, before g; reason: the constant is then uniform over all g with those symbol constants
--   - encoding: |∂_s^j ĝ(s)| ≤ C_j|s|^{−r−j} for |s| ≥ 1 → ĝ is C^{N_der} on {|s| ≥ 1}, with the derivatives taken within that closed set; reason: the display presupposes those derivatives; one-sided derivatives at |s| = 1 are the weakest reading
--   - encoding: jointly continuous on compact sets separated from x = 0, through the permitted order → jointly continuous on [a, b] × (ℝ∖{0}), for each order i ≤ J; reason: the same statement on a locally compact space; J is the order of the representative
--   - reading: If g = g_v is continuous as an L¹-valued function of v in a compact interval → a family g_v, v ∈ [a, b], each satisfying the hypotheses with the same constants C₀ and C_j, and L¹-continuous in v; reason: the sentence follows "Uniform symbol bounds yield uniform constants", and with v-dependent symbol constants the joint continuity fails (an L¹-small spike of height 1/|v − v₀| added to g_{v₀} keeps L¹ continuity but breaks pointwise continuity at v₀); Definition F.1 item 2 supplies uniform constants
-- source:
--   Wang–Zhang, Learning Mixtures with Unknown Scales: Sharp Dependence on Separation, STOC 2027 submission (sha256 5277f95e…), Lemma F.3, p.37 (PDF p.39)

import Mathlib
import Definitions.Def_MixScale_Regular

open MeasureTheory Filter Topology

namespace MixScale

/-- **Lemma F.3** (Dyadic local estimates).

S. Wang and X. Zhang, *Learning Mixtures with Unknown Scales: Sharp Dependence on Separation*, STOC
2027 submission manuscript (sha256 5277f95e…7c6c), Lemma F.3, p.37 (PDF p.39).

**Formalization Note.** "Uniform symbol bounds yield uniform constants": `C` is chosen after
`J, r, N_der` and the symbol constants, before `g`. The last sentence is the family clause, for `g v`
(`v ∈ [a, b]`) with the same symbol constants and `L¹`-continuous in `v`: there are representatives
with the same bounds and every spatial derivative through order `J` is jointly continuous in `(v, x)`
on `[a, b] × (ℝ ∖ {0})`, which is the same as jointly continuous on compact sets separated from `0`. -/
theorem lemma_F_3 (J : ℕ) (hJ : 1 ≤ J) (r : ℝ) (hr : 0 < r) (Nder : ℕ)
    (hN : max ((J : ℝ) + 1 - r) 0 < (Nder : ℝ)) (C0 : ℝ) (Cj : ℕ → ℝ) :
    ∃ C : ℝ, 0 < C ∧
      (∀ g : ℝ → ℝ, SymbolBounds r Nder C0 Cj g → ∃ gt : ℝ → ℝ, DyadicBounds J r C g gt) ∧
      ∀ (a b : ℝ) (g : ℝ → ℝ → ℝ), a ≤ b →
        (∀ v ∈ Set.Icc a b, SymbolBounds r Nder C0 Cj (g v)) →
        (∀ v ∈ Set.Icc a b, Tendsto (fun v' => ∫⁻ x, ENNReal.ofReal |g v' x - g v x|)
          (𝓝[Set.Icc a b] v) (𝓝 0)) →
        ∃ gt : ℝ → ℝ → ℝ, (∀ v ∈ Set.Icc a b, DyadicBounds J r C (g v) (gt v)) ∧
          ∀ i ≤ J, ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv i (gt p.1) p.2)
            (Set.Icc a b ×ˢ {x : ℝ | x ≠ 0}) := by sorry

end MixScale
