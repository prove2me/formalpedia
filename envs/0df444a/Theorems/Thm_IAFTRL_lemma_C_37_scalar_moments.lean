-- Prove2me | Theorems.Thm_IAFTRL_lemma_C_37_scalar_moments
-- name    : IAFTRL.lemma_C_37_scalar_moments
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-15T11:41:14.079307+00:00
-- url     : https://prove2.me/theorems/249c707d-5d90-41a1-b0c9-91123174723a
-- title:
--   Lemmas C.14, C.24–C.37 (v1) — scalar good events and local moments from the difference interface
-- statement:
--   This is the scalar probabilistic engine of the corrupted stochastic analysis of IA-FTRL, stated abstractly. It concerns $K$ real processes whose increments satisfy the full-history difference interface (C.226)–(C.228), and nothing else about the learner.
--
--   **Setting.** Fix $d\ge1$, $K$ actions with a distinguished action $a^*$, and gaps $\Delta(a^*)=0$ and $\Delta_0\le\Delta(a)\le2$ for $a\ne a^*$, where $\Delta_0\in(0,1]$. Let $\beta_t=16d+\sqrt{dt/(1+\log K)}$, $B=2^{25}\lceil256+\log(2K)\rceil$ and $c_R=\sqrt{d\log(eK)}$. On a probability space with $\sigma$-algebras $\mathcal F_0\subseteq\mathcal F_1\subseteq\cdots$, let $X_{t,a}$ be real processes with $X_{0,a}=0$, $X_{t+1,a}=X_{t,a}+D_{t,a}$ and $D_{t,a^*}=0$, where each $D_{t,a}$ is $\mathcal F_{t+1}$-measurable. Write
--   $$
--   Z_{t,a}=X_{t,a}-\min_bX_{t,b}.
--   $$
--   Let $\kappa_t\in[0,2]$ and $e_{t,a}$ be $\mathcal F_t$-measurable with $|e_{t,a}|\le2\kappa_t$, $|\Delta(a)+e_{t,a}|\le2$ and $\sum_{t<T}\kappa_t\le C$ almost surely. Assume that for all $t<T$ and all $a$:
--   $$
--   E[D_{t,a}\mid\mathcal F_t]=\Delta(a)+e_{t,a},\qquad |D_{t,a}|\le2\beta_{t+1}+\frac{Z_{t,a}+Z_{t,a^*}}B,\qquad E[D_{t,a}^2\mid\mathcal F_t]\le4\beta_{t+1}+\frac{2(Z_{t,a}^2+Z_{t,a^*}^2)}{B(t+1)} .
--   $$
--
--   **Claim.** There is an absolute constant $c_0>0$ such that for all such parameters there is a constant $M$, independent of the probability space, $T$, $C$ and the processes, with the following property. There are a moment order $P\ge8$ with $K\le2^P$, measurable events $G_t$ and numbers $\Psi_t\ge1$ such that for all $t<T$ and all $a\ne a^*$:
--
--   1. on $G_t$: $X_{t,a}\ge4(t+1)^{3/4}$;
--   2. $\displaystyle c_R\sum_{t<T}\frac{P(G_t^c)}{\sqrt{t+1}}\le c_0\sqrt{d\log K}\,\Delta_0^{-128/255}\sqrt C+M$;
--   3. $E\big[\mathbf 1_{G_t}\big((t+1)\Delta(a)/X_{t,a}\big)^P\big]\le8^P$;
--   4. $E\big[\mathbf 1_{G_t}\big(X_{t,a}/((t+1)\Delta(a))\big)^P\big]\le(8\Psi_t)^P$;
--   5. $\Psi_t\le M$ and $\sum_{t<T}(\Psi_t-1)/(t+1)\le M$,
--
--   where the random variables in 3–4 are integrable.
--
--   In the source the corruption-shifted negative moments are controlled first: Lemmas C.31 and C.33 and the burn-in absolute moments of Lemmas C.36 and C.37. These give the plateau windows and their failure probability (Lemmas C.27 and C.28), and then the positive compensated process of Lemma C.29 with its inverse and positive local moments (Lemmas C.30 and C.14). The events of Definition C.25 have the failure sum of Lemma C.24. With the interface of Lemma C.34 for IA-FTRL, this yields the per-action local moments used for the exploration, penalty and stability terms.
--
--   **Formalization Note** Rounds are 0-based (Lean round $t$ is the paper's round $t+1$). The moment order is called `p` in Lean, and $\min_bX_{t,b}$ is `⨅ b, X t b ω`. In the source $P=2\lceil256+\log(2K)\rceil$. Hypotheses are imposed only for $t<T$. The source extends the horizon by zero corruption to obtain full dyadic blocks; the bounds for rounds $t<T$ do not depend on that extension.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299v1, Appendix C.6.7–C.6.11: Definitions C.17, C.25, C.32, C.35 and Lemmas C.24, C.26–C.31, C.33, C.36, C.37; Lemma C.14 and (C.113)–(C.114) (p.66–90)

import Mathlib
import Definitions.Def_IAFTRL_beta
import Definitions.Def_IAFTRL_Bc
import Definitions.Def_IAFTRL_cR

namespace IAFTRL

open MeasureTheory

/-- **Scalar good events and local moments from the difference interface.** Zhao–Tan,
*Best-of-Both-Worlds FTRL for Linear Bandits*, arXiv:2611.01299v1, Appendix C.6.7–C.6.11: Definition
C.25, Lemmas C.24, C.26–C.31, C.33, C.36, C.37 and Lemma C.14 (with Definitions C.17, C.32, C.35).
The source states that these "scalar moment lemmas … use only" the row conditions; in the form used
by its proofs they are the full-history difference interface (C.226)–(C.228) of Lemma C.34:
"`X_{t+1,a} = X_{t,a} + D_{t,a}`, `E_{t−1}[D_{t,a}] = Δ(a) + e_{t,a}`, `|e_{t,a}| ≤ 2κ_t`,
`|D_{t,a}| ≤ 2β_t + (Z_{t,a} + M_t)/B`, `E_{t−1}[D²_{t,a}] ≤ 4β_t + 2(Z²_{t,a} + M²_t)/(Bt)`,
`|E_{t−1}[D_{t,a}]| ≤ 2`", with `M_t = max_a(−X_{t,a})`, `Z_{t,a} = X_{t,a} + M_t`, `X_{t,a*} = 0` and
`Σ_t κ_t ≤ C`.

Let `K` actions with a distinguished action `a*`, gaps `Δ(a*) = 0`, `Δ₀ ≤ Δ(a) ≤ 2` (`a ≠ a*`), and a
filtration `F_t` (Lean round `t`, paper round `t + 1`). Let `X_{t,a}` start at `0` with increments
`D_{t,a}` (`D_{t,a*} = 0`) that are `F_{t+1}`-measurable, and predictable `κ_t ∈ [0, 2]`, `e_{t,a}` with
`|e_{t,a}| ≤ 2κ_t`, `|Δ(a) + e_{t,a}| ≤ 2`, `Σ_{t<T} κ_t ≤ C` a.s., such that, with
`Z_{t,a} = X_{t,a} − min_b X_{t,b}`, `β = β_{t+1}`, `B = Bc K`:
`E[D_{t,a} | F_t] = Δ(a) + e_{t,a}`, `|D_{t,a}| ≤ 2β + (Z_{t,a} + Z_{t,a*})/B` and
`E[D²_{t,a} | F_t] ≤ 4β + 2(Z²_{t,a} + Z²_{t,a*})/(B(t+1))`. Then there are a moment order `P ≥ 8`
with `K ≤ 2^P`, measurable events `G_t` and `Ψ_t ≥ 1` such that for `t < T` and `a ≠ a*`:
1. on `G_t`, `X_{t,a} ≥ 4(t + 1)^{3/4}`;
2. `c_R Σ_{t<T} P(G_t^c)/√(t+1) ≤ c₀ √(d log K) Δ₀^{-128/255} √C + M`;
3. `E[1_{G_t} ((t+1)Δ(a)/X_{t,a})^P] ≤ 8^P` (Lemma C.30 with (C.113));
4. `E[1_{G_t} (X_{t,a}/((t+1)Δ(a)))^P] ≤ (8Ψ_t)^P` (Lemma C.14 with (C.113));
5. `Ψ_t ≤ M`, `Σ_{t<T} (Ψ_t − 1)/(t+1) ≤ M`.

**Formalization Note.** `c₀` is absolute; `M` is chosen after `(d, K, a*, Δ, Δ₀)` and before the
probability space, the filtration, `T`, `C` and the processes. The hypotheses are required only for
rounds `t < T`; `min_b X_{t,b}` is `⨅ b, X t b ω`. `P = 2⌈256 + log(2K)⌉` in the source. The source
extends the horizon by zero corruption to obtain full dyadic blocks (Definition C.17); the bound on
the events of rounds `t < T` does not depend on that extension. -/
theorem lemma_C_37_scalar_moments : ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ {d K : ℕ}, 1 ≤ d → ∀ (jstar : Fin K) (Δ : Fin K → ℝ) (Δ₀ : ℝ), 0 < Δ₀ → Δ₀ ≤ 1 →
      Δ jstar = 0 → (∀ a, a ≠ jstar → Δ₀ ≤ Δ a) → (∀ a, Δ a ≤ 2) →
      ∃ M : ℝ, ∀ {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (F : ℕ → MeasurableSpace Ω) (T : ℕ) (C : ℝ) (X D e : ℕ → Fin K → Ω → ℝ)
        (κ : ℕ → Ω → ℝ), 1 ≤ T → 0 ≤ C →
        (∀ t < T, F t ≤ mΩ ∧ F t ≤ F (t + 1)) →
        (∀ a ω, X 0 a ω = 0) → (∀ t a ω, X (t + 1) a ω = X t a ω + D t a ω) →
        (∀ t ω, D t jstar ω = 0) →
        (∀ t < T, ∀ a, Measurable[F (t + 1)] (D t a) ∧ Measurable (D t a)) →
        (∀ t < T, Measurable[F t] (κ t) ∧ ∀ a, Measurable[F t] (e t a)) →
        (∀ t < T, ∀ ω, 0 ≤ κ t ω ∧ κ t ω ≤ 2 ∧
          ∀ a, |e t a ω| ≤ 2 * κ t ω ∧ |Δ a + e t a ω| ≤ 2) →
        (∀ᵐ ω ∂P, ∑ t ∈ Finset.range T, κ t ω ≤ C) →
        (∀ t < T, ∀ a, P[D t a | F t] =ᵐ[P] fun ω => Δ a + e t a ω) →
        (∀ t < T, ∀ a ω, |D t a ω| ≤ 2 * beta d K (t + 1) +
          ((X t a ω - ⨅ b, X t b ω) + (X t jstar ω - ⨅ b, X t b ω)) / Bc K) →
        (∀ t < T, ∀ a, P[fun ω => D t a ω ^ 2 | F t] ≤ᵐ[P] fun ω => 4 * beta d K (t + 1) +
          2 * ((X t a ω - ⨅ b, X t b ω) ^ 2 + (X t jstar ω - ⨅ b, X t b ω) ^ 2) /
            (Bc K * ((t : ℝ) + 1))) →
        ∃ (G : ℕ → Set Ω) (p : ℕ) (Ψ : ℕ → ℝ), (∀ t, MeasurableSet (G t)) ∧
          8 ≤ p ∧ (K : ℝ) ≤ 2 ^ p ∧
          (∀ t < T, ∀ ω ∈ G t, ∀ a, a ≠ jstar → 4 * (t + 1 : ℝ) ^ ((3 : ℝ) / 4) ≤ X t a ω) ∧
          cR d K * ∑ t ∈ Finset.range T, (P (G t)ᶜ).toReal / Real.sqrt (t + 1) ≤
            c₀ * (Real.sqrt ((d : ℝ) * Real.log K) * Δ₀ ^ (-(128 : ℝ) / 255) * Real.sqrt C) +
              M ∧
          (∀ t < T, ∀ a, a ≠ jstar →
            Integrable ((G t).indicator fun ω => ((t + 1 : ℝ) * Δ a / X t a ω) ^ p) P ∧
            ∫ ω, (G t).indicator (fun ω => ((t + 1 : ℝ) * Δ a / X t a ω) ^ p) ω ∂P ≤ 8 ^ p) ∧
          (∀ t < T, ∀ a, a ≠ jstar →
            Integrable ((G t).indicator fun ω => (X t a ω / ((t + 1 : ℝ) * Δ a)) ^ p) P ∧
            ∫ ω, (G t).indicator (fun ω => (X t a ω / ((t + 1 : ℝ) * Δ a)) ^ p) ω ∂P ≤
              (8 * Ψ t) ^ p) ∧
          (∀ t < T, 1 ≤ Ψ t ∧ Ψ t ≤ M) ∧
          ∑ t ∈ Finset.range T, (Ψ t - 1) / (t + 1) ≤ M := by sorry

end IAFTRL
