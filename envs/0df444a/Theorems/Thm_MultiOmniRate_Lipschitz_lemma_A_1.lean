-- Prove2me | Theorems.Thm_MultiOmniRate_Lipschitz_lemma_A_1
-- name    : MultiOmniRate.Lipschitz.lemma_A_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:25:05.454702+00:00
-- url     : https://prove2.me/theorems/324b77c8-ec30-4c8b-8d25-2d959b12ff93
-- title:
--   Lemma A.1 — population correlation bounds for Algorithms 3 and 4 with probability $1-\delta$, extra $C\sqrt{n\log(2/\delta)}$
-- statement:
--   Fix $K\ge2$, $n\ge1$, $0<r\le1/2$ and $0<\delta<1$. Let $(x_t,y_t)_{t=1}^n$ be independent draws from $\mathcal D$. On each round choose the whole rule $q_t:\mathcal X\to\Delta_K$ using preceding examples, the current tests and randomness independent of the examples, before observing $(x_t,y_t)$. Each expectation over $\mathcal D$ holds the current prediction and test functions fixed. With an absolute constant $C$, each conclusion holds with probability at least $1-\delta$:
--
--   1. if $w_t$ is produced by Algorithm 3 (horizon $n$, width $r$, updates $(q_t(x_t),y_t)$), then
--   $$\sup_{\ell\in\mathcal L_{\mathrm{All}}}\Big|\sum_{t=1}^n\mathbb E_{(x,y)\sim\mathcal D}\langle w_{\ell,r}(q_t(x)),e_y-q_t(x)\rangle\Big|\le\sum_{t=1}^n\mathbb E_{(x,y)\sim\mathcal D}\langle w_t(q_t(x)),e_y-q_t(x)\rangle+C\,\mathrm{Reg}_{\mathrm{dec}}(n,r)+C\sqrt{n\log(2/\delta)};\quad(A.3)$$
--   2. for a fixed finite nonempty class $\mathcal H$ of maps $\mathcal X\to\Delta_K$, if $g_t$ is produced by Algorithm 4 (horizon $n$, accuracy $r$, updates $(x_t,q_t(x_t),y_t)$), then
--   $$\sup_{g\in\Delta\mathcal L_{\mathrm{Lip}}\circ\mathcal H}\Big|\sum_{t=1}^n\mathbb E_{\mathcal D}\langle g(x),e_y-q_t(x)\rangle\Big|\le\sum_{t=1}^n\mathbb E_{\mathcal D}\langle g_t(x),e_y-q_t(x)\rangle+C\,\mathrm{Reg}_{\Delta\mathcal L_{\mathrm{Lip}}\circ\mathcal H}(n)+C\sqrt{n\log(2/\delta)},\quad(A.4)$$
--
--   where $\mathrm{Reg}_{\mathrm{dec}}(n,r)=C_Knr+C_K\sqrt nf_K(r)$ is (3.4) and $\mathrm{Reg}_{\Delta\mathcal L_{\mathrm{Lip}}\circ\mathcal H}(n)=C_Knr+C_K\sqrt n(\sqrt{\log(2N)}+\beta_K(r))$ is the bound of (3.5).
--
--   This is the confidence version used for the second sentence of the main theorem.
--
--   Differences from the source:
--   - encoding: labels $\mathcal Y=\{0,\dots,K-1\}$ → `Fin K`, with `[NeZero K]` (implied by $K\ge2$) so that label $0$ exists; reason: relabeling; same instances
--   - encoding: rounds $t=1,\dots,n$ → rounds $t=0,\dots,n-1$ (`Finset.range n` or `Fin n`); reason: index shift only
--   - generalization: Algorithms 3 and 4 with covers "with the size bounds of Lemma 3.11" / "as in Lemma 3.15" → admissible covers (`Alg3Covers`, `Alg4Covers`) for every size constant $C_{\mathrm{cov}}>0$, with $C_K$ chosen after it; reason: the paper's constants are admissible values of $C_{\mathrm{cov}}$
--   - reading: "$C\,\mathrm{Reg}_{\mathrm{dec}}(n,r)$", "$C\,\mathrm{Reg}_{\Delta\mathcal L_{\mathrm{Lip}}\circ\mathcal H}(n)$" with (3.4), (3.5) → $C\cdot(C_Knr+C_K\sqrt nf_K(r))$ and $C\cdot(C_Knr+C_K\sqrt n(\sqrt{\log 2N}+\beta_K(r)))$: $C$ absolute and fixed first, one $C_K$ (depending on $K$, $C_{\mathrm{cov}}$) for both parts; reason: (3.4) and (3.5) carry existential constants depending only on $K$
--   - reading: "choose the whole rule $q_t$ using preceding examples, the current tests, and randomness independent of the examples" → a chooser $Q(\xi,t,(x_s,y_s)_{s<t})$ of measurable rules, with $\xi\sim P_\xi$ independent of $S\sim\mathcal D^n$; "with probability at least $1-\delta$" as: the failure set has outer measure at most $\delta$ under $\mathcal D^n\otimes P_\xi$; reason: the current tests of Algorithms 3–4 are functions of the preceding examples and $\xi$; measurable rules make $\mathbb E_{\mathcal D}$ defined
--   - encoding: a fixed finite nonempty class $\mathcal H$ of maps $\mathcal X\to\Delta_K$ → a family $h:\mathrm{Fin}\,N\to(\mathcal X\to\Delta_K)$, $N\ge1$, of measurable maps; reason: repetitions allowed; measurability is needed for $\mathbb E_{\mathcal D}\langle g(x),\cdot\rangle$
--   - encoding: $\mathcal L_{\mathrm{All}}$: arbitrary action spaces → `AllLoss.{u} K`: action spaces in a universe `u`, with a measurable structure; reason: $w_{\ell,r}$ and the Decision-OI term depend on $\ell$ only through $\ell^{\mathrm{pr}}$, which is itself a loss on $\Delta_K$, so every universe gives the same class
--   - encoding: $\ell\in\mathcal L_{\mathrm{Lip}}$ in $\Delta\mathcal L_{\mathrm{Lip}}\circ\mathcal H$ → pairs $(\ell,\mathrm{BR}_\ell)$ of `LLip K`; the test $x\mapsto\Delta\ell(h(x))$ uses $\ell$ only; reason: every Lipschitz loss has a measurable best response, so the class of tests is the same
--   - encoding: $\mathrm{Unif}(\Delta_K)$ → `unifSimplex K`: normalized Lebesgue measure on the free coordinates $(p_1,\dots,p_{K-1})$, pushed to $\Delta_K$; reason: the uniform distribution on the simplex, as in the proof of Lemma 3.3 (App. A.1)
-- source:
--   Rivkin, Okoroafor, Kim, The Sample Complexity of Multi-Class Omniprediction, STOC 2027 submission (manuscript sha256 135d9904…), pp. 58–59, Lemma A.1 (App. A.3)

import Mathlib
import Definitions.Def_MultiOmniRate_Lipschitz_Setting
import Definitions.Def_MultiOmniRate_Lipschitz_OmniErrors
import Definitions.Def_MultiOmniRate_Lipschitz_Smoothing
import Definitions.Def_MultiOmniRate_Lipschitz_Learners

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace MultiOmniRate.Lipschitz

theorem lemma_A_1.{u, v, w} : ∃ C : ℝ, 0 < C ∧
    ∀ (K : ℕ) [NeZero K], 2 ≤ K → ∀ (Ccov : ℝ), 0 < Ccov → ∃ CK : ℝ, 0 < CK ∧
    ∀ (X : Type v) [MeasurableSpace X] (D : Measure (X × Fin K)) [IsProbabilityMeasure D]
      (n : ℕ), 1 ≤ n → ∀ (r : ℝ), 0 < r → r ≤ 1 / 2 → ∀ (δ : ℝ), 0 < δ → δ < 1 →
    ∀ (Ξ : Type w) [MeasurableSpace Ξ] (Pξ : Measure Ξ) [IsProbabilityMeasure Pξ]
      (Q : Ξ → (t : ℕ) → (Fin t → X × Fin K) → X → Simplex K),
      (∀ ξ t hist, Measurable (Q ξ t hist)) →
    (∀ (B : ℕ → Finset (Simplex K → Fin K → ℝ)), Alg3Covers.{u} K r Ccov B →
      ((Measure.pi fun _ : Fin n => D).prod Pξ)
        {Sξ | ¬ ((⨆ ℓ : AllLoss.{u} K, |∑ t : Fin n, ∫ xy, dot
              (smoothW r ℓ.ℓ.pr (ruleOf Q Sξ.2 Sξ.1 t xy.1))
              (resid xy.2 (ruleOf Q Sξ.2 Sξ.1 t xy.1)) ∂D|) ≤
            ∑ t : Fin n, ∫ xy, dot
              (chainOutH B n r (decHistOf Q Sξ.2 Sξ.1 t) (ruleOf Q Sξ.2 Sξ.1 t xy.1))
              (resid xy.2 (ruleOf Q Sξ.2 Sξ.1 t xy.1)) ∂D +
              C * (CK * n * r + CK * Real.sqrt n * fK K r) +
              C * Real.sqrt (n * Real.log (2 / δ)))} ≤ ENNReal.ofReal δ) ∧
    (∀ (N : ℕ), 1 ≤ N → ∀ (h : Fin N → X → Simplex K), (∀ i, Measurable (h i)) →
      ∀ (B : ℕ → Finset (X → Fin K → ℝ)), Alg4Covers K h r Ccov B →
      ((Measure.pi fun _ : Fin n => D).prod Pξ)
        {Sξ | ¬ ((⨆ g : testClass (LLip K) (Set.range h), |∑ t : Fin n, ∫ xy, dot
              ((g : X → Fin K → ℝ) xy.1) (resid xy.2 (ruleOf Q Sξ.2 Sξ.1 t xy.1)) ∂D|) ≤
            ∑ t : Fin n, ∫ xy, dot (chainOutH B n r (hypHistOf Q Sξ.2 Sξ.1 t) xy.1)
              (resid xy.2 (ruleOf Q Sξ.2 Sξ.1 t xy.1)) ∂D +
              C * (CK * n * r + CK * Real.sqrt n *
                (Real.sqrt (Real.log (2 * N)) + hypBracket K r)) +
              C * Real.sqrt (n * Real.log (2 / δ)))} ≤ ENNReal.ofReal δ) := by sorry

end MultiOmniRate.Lipschitz
