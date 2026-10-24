-- Prove2me | Theorems.Thm_OfflineCMC_Minimax_proposition_3
-- name    : OfflineCMC.Minimax.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:39:20.007146+00:00
-- url     : https://prove2.me/theorems/d14b770a-a6df-40a3-92d8-f65a3dededd3
-- title:
--   Proposition 3 (corrected: n_low ≤ m/(2T), n_high ≥ mζ^(max)) — Bernstein bound for the visit counts N^(l)_s under Assumptions 1, 2, 4
-- statement:
--   There is a function $C\mapsto\mathbb C_{pel}(C)$, positive on $(1,\infty)$, with the following property.
--
--   Let $\{(X_i,a_i)\}$ be any controlled Markov chain satisfying Assumption 1 (constants $\zeta_1,\zeta_2$), Assumption 2 (integer $T$) and Assumption 4 (constant $\mathbb C_\Delta$) on the window up to $m$. Put $\mathbb C_{pel}=\mathbb C_{pel}(\mathbb C_\Delta)$ and $\zeta^{(\max)}=\max\{\zeta_1,1-\zeta_2\}$, and let $\rho^{(l)}_s=\sup_{1\le i\le m}\mathbb P(X_i=s,a_i=l)$. Then for every pair $(s,l)$ and all integers $n_{low}\le m/(2T)$ and $n_{high}\ge m\zeta^{(\max)}$,
--   $$
--   \begin{aligned}
--   \mathbb P\big(N^{(l)}_s\notin[n_{low},n_{high}]\big)\le{}&2\exp\Big(-\frac{\mathbb C_{pel}\,(n_{low}-\frac m{2T})^2}{4m\mathbb C_\Delta\rho^{(l)}_s+1+(\frac m{2T}-n_{low})(\log m)^2}\Big)\\
--   &+2\exp\Big(-\frac{\mathbb C_{pel}\,(n_{high}-m\zeta^{(\max)})^2}{4m\mathbb C_\Delta\rho^{(l)}_s+1+(n_{high}-m\zeta^{(\max)})(\log m)^2}\Big).
--   \end{aligned}
--   $$
--
--   This is a Bernstein-type tail bound for the visit counts of a geometrically mixing controlled Markov chain. The dependence on the chain enters only through $\rho^{(l)}_s$, $T$, $\zeta^{(\max)}$ and the constant $\mathbb C_{pel}$, which depends on $\mathbb C_\Delta$ alone. Theorem 2 applies it with $n_{low}=m/(4T)$ and $n_{high}=m(1+\zeta^{(\max)})/2$.
--
--   **Formalization Note** $\mathbb C_{pel}$ is a function of $\mathbb C_\Delta$ chosen before the chain, $d$, $k$, $m$, $T$ and $\zeta$. The integers are in $\mathbb Z$. In the stated regime both denominators are at least $1$.
--
--   Differences from the source:
--   - correction: "for all integers $n_{low}<\mathbb E[N^{(l)}_s]<n_{high}$" → for all integers $n_{low}\le m/(2T)$ and $n_{high}\ge m\zeta^{(\max)}$; reason: the printed statement is false when $n_{low}>m/(2T)$, where the first denominator uses the negative proxy $m/(2T)-n_{low}$. Take one control, $X_i$ i.i.d. on two states with $\mathbb P(X_i=s)=p$, $m=30$, $T=4$, $\mathbb C_\Delta=2$ ($\bar\eta\equiv0$), $S_i=\{s\}$, $n_{low}=13$, $n_{high}=10^6$, and $p\downarrow p^*\approx0.4417$, the root of $240p+1=(13-3.75)(\log30)^2$. The first denominator tends to $0^+$, so the right side tends to $0$ for every $\mathbb C_{pel}>0$, while $\mathbb P(N<13)\approx0.39$.
--   - reading: "a positive constant $\mathbb C_{pel}$ depending only upon $\mathbb C_\Delta$" → a function $\mathbb C_{pel}(\cdot)$, positive on $(1,\infty)$, quantified before the chain; reason: this is the meaning of "depending only upon $\mathbb C_\Delta$"
--   - reading: first hitting time with "$(X_j\ne s,a_j\ne l)$" → first time $n\ge1$ with $(X_n,a_n)=(s,l)$, inside Assumption 2; reason: as in the recursive clause of Definition 2
--   - reading: Assumption 4 for $i<j$ → for $0\le i<j\le m$ (empty history at $i=0$); reason: eq. (2.1) defines $\bar\eta_{i,j}$ for $i<j\le m$ with $\hbar^{i-1}_0\in(\chi\times\mathbb I)^i$
--   - generalization: Assumption 1 for all times → at the times $1\le i\le m$; reason: weaker hypothesis implied by the paper's
--   - generalization: Assumption 4 with "$\mathbb C_\Delta>1$ independent of $m$" → the bound on $\bar\eta_{i,j}$ (window up to $m$) at the given sample size $m$ only; reason: a weaker hypothesis implied by the paper's; $\mathbb C_{pel}$ still depends on $\mathbb C_\Delta$ alone, so the statement specializes to the source's
--   - encoding: Assumption 2's supremum of conditional expectations → a.s. finite integrable return times and an $\omega$-dependent witness $T'<T$; reason: equivalent to the paper's bound
-- source:
--   Banerjee, Honnappa & Rao, Offline Estimation of Controlled Markov Chains: Minimaxity and Sample Complexity, arXiv:2211.07092v5, p. 12, Proposition 3 (ρ^(l)_s defined on p. 12)

import Mathlib
import Definitions.Def_OfflineCMC_Minimax_CMC
import Definitions.Def_OfflineCMC_Minimax_Model

universe u

namespace OfflineCMC.Minimax

open MeasureTheory

theorem proposition_3 :
    ∃ Cpel : ℝ → ℝ, (∀ x : ℝ, 1 < x → 0 < Cpel x) ∧
      ∀ {d k : ℕ} {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (C : CMC d k μ) (m : ℕ) (ζ₁ ζ₂ : ℝ) (T : ℕ) (CΔ : ℝ),
        C.Assumption1 m ζ₁ ζ₂ → C.Assumption2 T → C.Assumption4 m CΔ →
        ∀ (s : Fin d) (l : Fin k) (nlow nhigh : ℤ),
          (nlow : ℝ) ≤ (m : ℝ) / (2 * (T : ℝ)) →
          (m : ℝ) * zetaMax ζ₁ ζ₂ ≤ (nhigh : ℝ) →
          μ.real {ω | (C.count m l s ω : ℤ) < nlow ∨ nhigh < (C.count m l s ω : ℤ)} ≤
            2 * Real.exp (-(Cpel CΔ * ((nlow : ℝ) - (m : ℝ) / (2 * (T : ℝ))) ^ 2 /
                (4 * (m : ℝ) * CΔ * C.rho m l s + 1 +
                  ((m : ℝ) / (2 * (T : ℝ)) - (nlow : ℝ)) * Real.log (m : ℝ) ^ 2))) +
            2 * Real.exp (-(Cpel CΔ * ((nhigh : ℝ) - (m : ℝ) * zetaMax ζ₁ ζ₂) ^ 2 /
                (4 * (m : ℝ) * CΔ * C.rho m l s + 1 +
                  ((nhigh : ℝ) - (m : ℝ) * zetaMax ζ₁ ζ₂) * Real.log (m : ℝ) ^ 2))) := by sorry

end OfflineCMC.Minimax
