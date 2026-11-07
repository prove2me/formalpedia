-- Prove2me | Theorems.Thm_HZTractability_lemma_4_10
-- name    : HZTractability.lemma_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:16:32.829201+00:00
-- url     : https://prove2.me/theorems/df087dc4-4af3-4490-a2a9-36be6c18069b
-- title:
--   Lemma 4.10 — global decoding
-- statement:
--   Fix a rational $a\in(0,1)$. There are positive rational constants $\tau_a\le\kappa/100$, $\zeta_a$, $e_a$ and an integer $K_a\ge1$, depending only on $a$, such that for every admissible $K\ge K_a$: if a normalized additive $\varepsilon$-equilibrium of $M(G;a,\tau_a,K)$ (with $G$ nonempty, satisfying (2), and equalized group prices) satisfies
--   $$
--   \varepsilon\le e_a/K^2,\qquad \mathcal W\le\zeta_a,
--   $$
--   then its decoded vector is a $\kappa$-threshold solution of $G$. The constants can be chosen so that $\varepsilon\le e_a/K^2$ also implies the hypotheses of Lemma 4.9: there are constants $d_a,g_a,c_a,C_a$ of Lemma 4.9 such that $e_a/K^2\le\min\{c_a,1/(C_aK)\}$ and the conclusions of Lemma 4.9 hold for every admissible $K\ge K_a$.
--
--   Together with Lemma 4.9 this gives Theorem 4.1.
--
--   Differences from the source:
--   - encoding: $O_a(\cdot)$ terms and “sufficiently large” / small-error thresholds, constants depending only on $a$ → one block of existential constants (a threshold $K_a$ or $K_0$, a smallness constant, a multiplier $C_1$) chosen before $K,\tau,G,\varepsilon,\zeta$, the equilibrium and $v$; reason: the paper's convention: constants depend only on $a$, uniformly over the graph, admissible $K$ and $0<\tau\le\kappa/100$ (pp.6, 17, 38)
--   - reading: “The constants can be chosen so that $\varepsilon\le e_a/K^2$ also implies the hypotheses of Lemma 4.9” → the same existential block contains constants $d_a,g_a,c_a,C_a$ for which Lemma 4.9 holds for every admissible $K\ge K_a$ and $e_a/K^2\le\min\{c_a,1/(C_aK)\}$; reason: the sentence is part of the lemma's statement; its proof (p.19) takes $e_a\le\min\{c_a,1/C_a\}$ and enlarges $K_a$
-- source:
--   Panageas, Shein, Taherijam, Vazirani, Exploring the Tractability Frontier of Hylland–Zeckhauser Models, arXiv:2610.35848 (held version, sha256 74b7bf9f…), Lemma 4.10, p.18 (PDF p.20); standing assumptions of §4.5, p.17

import Mathlib
import Definitions.Def_HZTractability_kappa
import Definitions.Def_HZTractability_admissible
import Definitions.Def_HZTractability_Lp
import Definitions.Def_HZTractability_ThrGraph
import Definitions.Def_HZTractability_Market
import Definitions.Def_HZTractability_IsUnitBundle
import Definitions.Def_HZTractability_IsNormAddEq
import Definitions.Def_HZTractability_decode
import Definitions.Def_HZTractability_IsThresholdSol
import Definitions.Def_HZTractability_Wcal

namespace HZTractability

/-- **Lemma 4.10 (Global decoding)** (Panageas–Shein–Taherijam–Vazirani, arXiv:2610.35848, held
version, sha256 74b7bf9f…, p.18 (PDF 20)): "There are positive rational constants τ_a ≤ κ/100, ζ_a,
e_a, and an integer K_a ≥ 1, depending only on a, such that the following holds for every
admissible K ≥ K_a. If a normalized additive ε-equilibrium of M(G; a, τ_a, K) satisfies
ε ≤ e_a/K², 𝒲 ≤ ζ_a, then its decoded vector is a κ-threshold solution of G. The constants can be
chosen so that ε ≤ e_a/K² also implies the hypotheses of Lemma 4.9."

The statement has three parts, all with one choice of constants depending only on `a` (including
the constants `d_a, g_a, c_a, C_a` of Lemma 4.9):
1. decoding: for admissible `K ≥ K_a`, every nonempty `G` satisfying (2), and every normalized
   additive ε-equilibrium of `M(G; a, τ_a, K)` with equalized group prices, `0 ≤ ε ≤ e_a/K²` and
   `𝒲 ≤ ζ_a`, the decoded vector (4) is a κ-threshold solution of `G`;
2. for admissible `K ≥ K_a`, `e_a/K² ≤ min{c_a, 1/(C_a K)}`;
3. Lemma 4.9 holds with these constants for every admissible `K ≥ K_a`.

**Formalization Note** Equalized prices are the standing assumption of §4.5 (p.17). The last
sentence of the lemma is parts 2–3: `K_a` is a valid "sufficiently large" threshold for Lemma 4.9
and `e_a/K²` lies below its error bound. `κ = 1/200`. -/
theorem lemma_4_10 (a : ℚ) (ha0 : 0 < a) (ha1 : a < 1) :
    ∃ (τa ζa ea : ℚ) (Ka : ℕ) (d g c Ca : ℚ),
      0 < τa ∧ τa ≤ kappa / 100 ∧ 0 < ζa ∧ 0 < ea ∧ 1 ≤ Ka ∧
      0 < d ∧ 0 < g ∧ 0 < c ∧ 0 < Ca ∧
      (∀ K : ℕ, admissible a K → Ka ≤ K → ∀ G : ThrGraph, 1 ≤ G.n → G.Cond2 →
        ∀ (ε : ℝ) (x : Buyer a τa K G → Good a τa K G → ℝ) (p : Good a τa K G → ℝ),
          0 ≤ ε → ε ≤ (ea : ℝ) / (K : ℝ) ^ 2 →
          IsNormAddEq (mkt a τa K G) ε x p → IsGroupEqualized p →
          Wcal (mkt a τa K G) x p ≤ ζa →
          IsThresholdSol (kappa : ℝ) G (decode p)) ∧
      (∀ K : ℕ, admissible a K → Ka ≤ K →
        (ea : ℝ) / (K : ℝ) ^ 2 ≤ min (c : ℝ) (1 / ((Ca : ℝ) * K))) ∧
      (∀ K : ℕ, admissible a K → Ka ≤ K →
        ∀ τ : ℚ, 0 < τ → τ ≤ kappa / 100 → ∀ G : ThrGraph, 1 ≤ G.n → G.Cond2 →
        ∀ (ε : ℝ) (x : Buyer a τ K G → Good a τ K G → ℝ) (p : Good a τ K G → ℝ),
          0 ≤ ε → ε ≤ min (c : ℝ) (1 / ((Ca : ℝ) * K)) →
          IsNormAddEq (mkt a τ K G) ε x p → IsGroupEqualized p →
          Wcal (mkt a τ K G) x p ≤ (Ca : ℝ) * Fintype.card (Buyer a τ K G) * ε ∧
          (∀ j, (∃ i, mkt a τ K G i j = 1) → 1 + (d : ℝ) < p j) ∧
          ∀ i y, IsUnitBundle p y → ∑ j, mkt a τ K G i j * y j ≤ 1 - (g : ℝ)) := by sorry

end HZTractability
