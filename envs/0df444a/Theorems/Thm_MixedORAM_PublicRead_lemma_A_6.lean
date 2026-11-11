-- Prove2me | Theorems.Thm_MixedORAM_PublicRead_lemma_A_6
-- name    : MixedORAM.PublicRead.lemma_A_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:48:47.919798+00:00
-- url     : https://prove2.me/theorems/1d37644d-a6cf-4fc5-997b-5c0586bd4c93
-- title:
--   Lemma A.6 — epoch charging: Y ≥ c, Y log₂(2 + X/Y) ≥ c₁h*, and Φ(X, Y) ≥ c₂h* when X ≥ c₀
-- statement:
--   Fix constants $c,\eta,g>0$. There is $c_1>0$, and for every $c_0>0$ a $c_2>0$, depending only on these, such that the following holds. Fix an implementation, an initial array, an IID request law, a prefix length $N$ and let $T_N$ be the average total cost of the first $N$ requests. Fix a window length $\omega$ and a shortest epoch length $\ell_0\ge1$ with $\omega\ge2\ell_0$, and put $h_*=\log_2(2+\omega/\ell_0)$. Consider a reference experiment that draws an endpoint $e$ uniformly from a set $V$ of at least $N/4$ positions with $\omega\le e\le N$, draws the reference prefix of length $e$ conditioned on an event $G_0$ whose probability is at least $g$, and appends a terminal block of at most two requests with expected probe count $Y$. For an epoch $I$ in the window at a fixed position relative to $e$, let $E_I$ and $D_I$ count the dependency edges from $I$ into the younger requests and into the terminal block. Suppose that for a density of fresh words $d>0$, every epoch $I$ of length $\ell\ge\ell_0$ in the window satisfies
--   $$\mathbb E D_I+\frac{\mathbb E E_I}{\eta d\ell}\ \ge\ c,$$
--   with the expectations over the conditioned experiment. Put $X=T_N/d$. Then
--
--   1. $Y\ge c$;
--   2. $Y\log_2(2+X/Y)\ge c_1h_*$;
--   3. if additionally $X\ge c_0$, then $\Phi(X,Y)\ge c_2h_*$.
--
--   This converts the per-epoch bound (11) into the logarithmic tradeoffs of the paper.
--
--   Differences from the source:
--   - reading: an endpoint e ≥ ω drawn uniformly from a set V of at least N/4 positions → a finite set V with ω ≤ e ≤ N for every e ∈ V and N ≤ 4|V|; reason: the positions are those of the prefix of length N whose average cost is T_N; the proof bounds the prefix's edges by N·T_N, which needs e ≤ N
--   - encoding: a reference experiment with a conditioning event G₀ and a terminal block of at most two requests → termExp for any IID request law δ, any event G₀(e, prefix) with Pr(G₀) ≥ g, any law of terminal blocks of length ≤ 2 depending on (e, prefix); reason: the paper's abstract experiment, written for the ORAM model of the mission
--   - encoding: every epoch I of length ℓ ≥ ℓ₀ in the window at a fixed position relative to e → offsets (s, ℓ) with ℓ₀ ≤ ℓ, s + ℓ ≤ ω; reason: the epoch [e − s − ℓ + 1, e − s] lies in the window [e − ω + 1, e]
--   - encoding: shortest epoch length ℓ₀ → ℓ₀ ≥ 1; reason: an epoch has positive length and ω/ℓ₀ must be defined
--   - encoding: real X, Y and the conclusions (i)–(iii) → X = T_N/d and Y in [0, ∞]; (i) in [0, ∞]; (ii), (iii) as real inequalities unless X = ∞ or Y = ∞, where their left sides are +∞; reason: no finiteness hypothesis is added
--   - reading: with constants depending only on c, η, g; c₂ also depending on c₀ → ∃ c₁ > 0, ∀ c₀ > 0, ∃ c₂ > 0, chosen before every other object; reason: the stated dependencies
-- source:
--   Ciszewski, Ragnoli, Access Cost Tradeoffs in Mixed-Mode Oblivious RAM, STOC 2027 submission (manuscript sha256 a4f849fd…), pp. 18–19, Lemma A.6 (Eq. (18))

import Mathlib
import Definitions.Def_MixedORAM_PublicRead_Epochs
import Definitions.Def_MixedORAM_PublicRead_Frontier

set_option autoImplicit false

namespace MixedORAM.PublicRead

theorem lemma_A_6 (c η g : ℝ) (hc : 0 < c) (hη : 0 < η) (hg : 0 < g) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ c₀ : ℝ, 0 < c₀ → ∃ c₂ : ℝ, 0 < c₂ ∧
      ∀ (n w m a : ℕ) (I : Impl n w m a) (A₀ : Fin n → BitVec w) (δ : PMF (Request n w))
        (N ω ℓ₀ : ℕ) (V : Finset ℕ) (G₀ : ℕ → List (Request n w) → Prop)
        (term : ℕ → List (Request n w) → PMF (List (Request n w))) (d : ℝ),
        1 ≤ ℓ₀ → 2 * ℓ₀ ≤ ω → (∀ e ∈ V, ω ≤ e ∧ e ≤ N) → (N : ℝ) ≤ 4 * V.card →
        ENNReal.ofReal g ≤ termProbG I A₀ δ V G₀ term →
        (∀ (e : ℕ) (u : List (Request n w)), ∀ τ ∈ (term e u).support, τ.length ≤ 2) →
        0 < d →
        (∀ s ℓ : ℕ, ℓ₀ ≤ ℓ → s + ℓ ≤ ω →
          ENNReal.ofReal c ≤
            termExp I A₀ δ V G₀ term (fun e _ res => (edgesD e s ℓ (traceOf res) : ENNReal)) +
              termExp I A₀ δ V G₀ term (fun e _ res => (edgesE e s ℓ (traceOf res) : ENNReal)) /
                ENNReal.ofReal (η * d * ℓ)) →
        let Y : ENNReal :=
          termExp I A₀ δ V G₀ term (fun e _ res => (terminalProbes e res : ENNReal))
        let X : ENNReal := TN I A₀ δ N / ENNReal.ofReal d
        let hstar : ℝ := Real.logb 2 (2 + (ω : ℝ) / ℓ₀)
        ENNReal.ofReal c ≤ Y ∧
          (Y = ⊤ ∨ X = ⊤ ∨ c₁ * hstar ≤ Y.toReal * Real.logb 2 (2 + X.toReal / Y.toReal)) ∧
          (ENNReal.ofReal c₀ ≤ X → X = ⊤ ∨ Y = ⊤ ∨ c₂ * hstar ≤ Phi X.toReal Y.toReal) := by sorry

end MixedORAM.PublicRead
